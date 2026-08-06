/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Modules
import CatCrypt.NonUniform.Conditional
import CatCrypt.NonUniform.Product

/-!
# EasyCrypt import: lowering to `SPComp`

This module lowers the EasyCrypt AST (`Ast.lean`) to CatCrypt's semantic model
`SPComp`, the target of the pRHL / advantage logic. It covers typed local
assignment, uniform sampling, reads and writes of module globals, conditionals,
bounded `forN` loops, argument-free `call`s, and procedure calls resolved
against a `ProcEnv`; on top of statements it lowers procedures, concrete
modules, functors, and games.

## Lowering strategy: direct fold, hax-aligned target

The importer lowers directly to `SPComp`. It is a structural translation into
`SPComp` do-notation, threading a meta-level valuation `Env` of the local
variables. Loops and calls are **not** routed through the hax `ImpExpr` phases
(`dropReferences`, `localMutation`, `functionalizeLoops`, `cfIntoMonads`):
`ImpExpr` is a deterministic IR with no sampling constructor, so a game that
samples inside a loop — every multi-query cryptographic experiment — has no
`ImpExpr` image at all, and manufacturing one would mean extending `ImpExpr`
with a sampling arm and re-proving all four phase-correctness results and both
semantics against it. The direct lowering avoids that: it produces the same fold
image the hax loop phase yields.

Concretely, a bounded loop lowers to `SPComp.foldM env (List.replicate n step)`.
The hax `functionalizeLoops` phase rewrites a `for` loop to a `for_fold` node
whose denotation `denoteForLoop'` is a bounded index recursion over `[lo, hi)`
that runs the body once per index and threads the accumulator (base case at
`lo ≥ hi` returns the accumulator; the step runs the body then recurses at
`lo + 1`). The canonical `n`-fold monadic iteration `iterateM` has exactly that
two-equation shape, and `foldM_replicate_eq_iterateM` proves the importer's
`SPComp.foldM env (List.replicate n step)` equals it. The agreement lemma
`forN_lowering_agrees_hax_foldImage` is that equation specialized to the loop
step the importer emits — it witnesses that the direct lowering produces the fold
image `functionalizeLoops` targets. (The hax denotation lives in a deterministic
state monad `StateM Env Outcome` over hax's own value type, not in `SPComp`, so
the correspondence is stated over the shared `iterateM` shape rather than as a
cross-monad equation; `iterateM` is the compatibility bridge between the two.)
The matching relational rule `rHoare_foldM` (`Relational/Rules.lean`) is the
loop-congruence rule imported `while I` proofs apply.

## Memory: locals versus globals

Local variables live in the meta-level valuation `Env : String → EcVal`, so a
local assignment is functional rebinding and never touches the heap — the same
treatment hax's `localMutation` phase gives Rust locals. A module global lives in
the CatCrypt `Heap`, at the `GLocation` its `EcGlobal` denotes, read and written
by `SPComp.gget` / `SPComp.gset`, which code the value through `gencode`. At a
finite code that cell is also a `Location`, and `gencode` is there the `Fintype`
encoding `SPComp.get` / `SPComp.set` use, so the lowering of a finite-typed
global is equally a read and a write in the finite-typed vocabulary:
`lowerStmts_load_finLoc` and `lowerStmts_store_finLoc`.

## Lowering scheme

* `x <- e`            → functional rebinding `env ↦ env[x := ⟦e⟧ env]`;
* `x <$ t`            → `t.sampleFin` bound into the continuation;
* `x <$ d`            → `sampleFrom (⟦d⟧ env)` bound into the continuation, where
  `⟦d⟧` is `evalDistr`, the `SDistr` a distribution expression denotes;
* `x <- g`            → `SPComp.gget g.loc` bound into the continuation;
* `g <- e`            → `SPComp.gset g.loc (⟦e⟧ env)`;
* `if c then s else s'` → a Lean-level `if` on `⟦c⟧ env` over the lowered blocks;
* `for i = 0 to n-1 do body` → `SPComp.foldM env (List.replicate n step)`;
* `p()`               → inline the lowered body of `p`; nested calls expand up to
  the depth bound `fuel` (a call reached at `fuel = 0` is a no-op);
* `x <@ q(a)`         → `ρ q s (⟦a⟧ env)` bound into the continuation, where `ρ`
  is the ambient resolution environment;
* `return e`          → `SPComp.pure (⟦e⟧ env)` on the final valuation.

The `fuel` argument bounds argument-free call nesting so the lowering is total.
For a non-recursive procedure table any `fuel` at least the maximum call depth
yields exact inlining. Calls through a `ProcEnv` consume no fuel: they resolve to
an already-lowered `SPComp` procedure rather than being inlined syntactically.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open CatCrypt.Core

/-! ## Local valuations -/

/-- A local-variable valuation: a dynamically typed value per variable identity.
The key is an `EcVarId` — a source name together with the uniqueness stamp of a
bound identifier — so a program variable and a distribution operator's lambda
binder of one source name occupy different entries, and a binder cannot capture an
occurrence of another identifier of its name. -/
abbrev Env := EcVarId → EcVal

/-- The initial valuation: every variable holds the unit value until assigned. -/
def emptyEnv : Env := fun _ => EcVal.nil

/-- Rebind variable `x`, leaving all other variables unchanged. -/
def Env.update (env : Env) (x : EcVarId) (v : EcVal) : Env :=
  fun y => if y = x then v else env y

/-- Read variable `x` at the type code `t`; a variable holding a value of a
different type reads as `default`. -/
def Env.read (env : Env) (t : EcTy) (x : EcVarId) : t.interp := (env x).get t

@[simp] theorem Env.update_same (env : Env) (x : EcVarId) (v : EcVal) :
    env.update x v x = v := if_pos rfl

theorem Env.update_ne (env : Env) (x y : EcVarId) (v : EcVal) (h : y ≠ x) :
    env.update x v y = env y := if_neg h

@[simp] theorem Env.read_update_same (env : Env) (t : EcTy) (x : EcVarId) (v : t.interp) :
    (env.update x ⟨t, v⟩).read t x = v := by
  rw [Env.read, Env.update_same, EcVal.get_mk]

theorem Env.read_update_ne (env : Env) (t : EcTy) (x y : EcVarId) (v : EcVal) (h : y ≠ x) :
    (env.update x v).read t y = env.read t y := by
  rw [Env.read, Env.update_ne _ _ _ _ h, Env.read]

/-- A program variable and a bound identifier of the same source name are
different keys, so a binder's rebinding leaves the program variable of its name
readable. -/
theorem Env.read_update_stamped (env : Env) (t u : EcTy) (x : String) (s : Nat)
    (v : u.interp) :
    (env.update { name := x, stamp := some s } ⟨u, v⟩).read t (EcVarId.ofName x)
      = env.read t (EcVarId.ofName x) :=
  Env.read_update_ne _ _ _ _ _ (by simp [EcVarId.ofName])

/-- Bind a procedure's formal parameters at call entry, and a destructuring
assignment's names to their components: the value is typed by the components'
types as a right-nested product, and each binder takes its component in
declaration order — no names bind nothing, one name binds the whole value,
and the head of a longer list binds the product's first component before the
tail recurses on the second. When the names outnumber the value's components —
a shape the decoder's cross-checks reject — the head binds the whole remaining
value and the tail is left unbound. The recursion is structural on the name
list, so every arm reduces definitionally. -/
def bindParams (t : EcTy) (xs : List String) (a : t.interp) (env : Env) : Env :=
  match xs with
  | [] => env
  | x :: xs =>
    match xs with
    | [] => env.update x ⟨t, a⟩
    | _ :: _ =>
      match t, a with
      | .prod u v, a => bindParams v xs a.2 (env.update x ⟨u, a.1⟩)
      | t, a => env.update x ⟨t, a⟩
termination_by structural xs

@[simp] theorem bindParams_nil (t : EcTy) (a : t.interp) (env : Env) :
    bindParams t [] a env = env := rfl

@[simp] theorem bindParams_single (t : EcTy) (x : String) (a : t.interp)
    (env : Env) : bindParams t [x] a env = env.update x ⟨t, a⟩ := rfl

@[simp] theorem bindParams_cons₂ {u v : EcTy} (x y : String) (ys : List String)
    (a : (EcTy.prod u v).interp) (env : Env) :
    bindParams (.prod u v) (x :: y :: ys) a env
      = bindParams v (y :: ys) a.2 (env.update x ⟨u, a.1⟩) := rfl

/-! ## Expressions -/

/-- Pure evaluation of a typed expression against a local valuation.

Evaluation is computable, which is what the `#guard` checks of the golden
fixtures evaluate. The arms that compare values — the equality test, the
finite-map lookups, list and finite-set membership, and set union — need
decidable equality on a code the expression carries, which the `distr` code
does not have, so each branches on `EcTy.hasEq` of that code and takes
`decEqOfHasEq` on the true branch. The false branch is unreachable for every
decoded expression: `decodeExpr` rejects an equality at a code outside
`hasEq` and rejects list membership at such an element code, and `decodeTy`
rejects a finite-map type whose key code and a finite-set type whose element
code are outside it, so no decoded program carries one of these operations at
a code without decidable equality. It is reachable from a hand-written literal,
and answers there with the value named in the arm: the supplied default for
`mapGetD`, `false` for the three membership tests and the equality, and the
empty set for `fsetUnion`. Those answers are not the operations' meanings —
they are what a total computable function returns where the operation has no
meaning — so a hand-written literal at such a code states nothing about the
operation. -/
def evalExpr : {t : EcTy} → EcExpr t → Env → t.interp
  | _, .var t x,   env => env.read t x
  | _, .lit v,     _   => v
  | _, .bnot e,    env => !(evalExpr e env)
  | _, .band a b,  env => (evalExpr a env) && (evalExpr b env)
  | _, .bxor a b,  env => xor (evalExpr a env) (evalExpr b env)
  | _, .beq (t := u) a b, env =>
      if h : u.hasEq = true then
        letI := decEqOfHasEq u h
        decide (evalExpr a env = evalExpr b env)
      else false
  | _, .pair x y,  env => (evalExpr x env, evalExpr y env)
  | _, .fst p,     env => (evalExpr p env).1
  | _, .snd p,     env => (evalExpr p env).2
  | _, .finAdd (n := n) a b, env =>
      (show Fin n from evalExpr a env) + (show Fin n from evalExpr b env)
  | _, .intAdd a b, env =>
      (show Int from evalExpr a env) + (show Int from evalExpr b env)
  | _, .intMul a b, env =>
      (show Int from evalExpr a env) * (show Int from evalExpr b env)
  | _, .intOpp a, env => -(show Int from evalExpr a env)
  | _, .intEdivz a b, env =>
      (Int.ediv (show Int from evalExpr a env) (show Int from evalExpr b env),
       Int.emod (show Int from evalExpr a env) (show Int from evalExpr b env))
  | _, .intAbsz a, env => (Int.natAbs (show Int from evalExpr a env) : Int)
  | _, .intGcd a b, env =>
      (Int.gcd (show Int from evalExpr a env) (show Int from evalExpr b env) : Int)
  | _, .intLe a b, env =>
      decide ((show Int from evalExpr a env) ≤ (show Int from evalExpr b env))
  | _, .mapSet (a := a) (b := b) m k v, env =>
      EcTy.mapSet (a := a) (b := b) (evalExpr m env) (evalExpr k env) (evalExpr v env)
  | _, .mapMem (a := a) (b := b) m k, env =>
      if h : a.hasEq = true then
        EcTy.mapMem (a := a) (b := b) (evalExpr m env) (evalExpr k env) h
      else false
  | _, .mapGetD (a := a) (b := b) m k d, env =>
      if h : a.hasEq = true then
        EcTy.mapGetD (a := a) (b := b) (evalExpr m env) (evalExpr k env)
          (evalExpr d env) h
      else evalExpr d env
  | _, .ite c thn els, env =>
      if evalExpr c env then evalExpr thn env else evalExpr els env
  | _, .someE (a := a) x, env => EcTy.someVal (a := a) (evalExpr x env)
  | _, .optionGetD (a := a) o d, env =>
      EcTy.optionGetD (a := a) (evalExpr o env) (evalExpr d env)
  | _, .listCons (a := a) x l, env =>
      EcTy.listCons (a := a) (evalExpr x env) (evalExpr l env)
  | _, .listRcons (a := a) l x, env =>
      EcTy.listRcons (a := a) (evalExpr l env) (evalExpr x env)
  | _, .listSize (a := a) l, env => EcTy.listSize (a := a) (evalExpr l env)
  | _, .listMem (a := a) l x, env =>
      if h : a.hasEq = true then
        EcTy.listMem (a := a) (evalExpr l env) (evalExpr x env) h
      else false
  | _, .listNth (a := a) d l i, env =>
      EcTy.listNth (a := a) (evalExpr d env) (evalExpr l env) (evalExpr i env)
  | _, .fsetSingle (a := a) x, env => EcTy.fsetSingle (a := a) (evalExpr x env)
  | _, .fsetUnion (a := a) s t, env =>
      if h : a.hasEq = true then
        EcTy.fsetUnion (a := a) (evalExpr s env) (evalExpr t env) h
      else EcTy.defaultOf (.fset a)
  | _, .fsetMem (a := a) s x, env =>
      if h : a.hasEq = true then
        EcTy.fsetMem (a := a) (evalExpr s env) (evalExpr x env) h
      else false

/-- Evaluate a boolean-typed expression to a `Bool`, the form a Lean-level `if`
branches on. -/
def evalCond (c : EcExpr .bool) (env : Env) : Bool := evalExpr c env

@[simp] theorem evalCond_eq (c : EcExpr .bool) (env : Env) :
    evalCond c env = evalExpr c env := rfl

/-! ## Uniform sampling at a finite code -/

/-- Uniform sampling at a code whose interpretation is finite. `SPComp.sample` is
uniform over its carrier, so the finiteness proof is what makes the sampler
exist. -/
noncomputable def EcTy.sampleFin (t : EcTy) (h : t.isFin = true) : SPComp t.interp :=
  letI := t.fintypeOfIsFin h
  SPComp.sample t.interp

/-- Uniform sampling at the code `bool` is uniform sampling of `Bool`. -/
@[simp] theorem sampleFin_bool (h : EcTy.bool.isFin = true) :
    EcTy.bool.sampleFin h = SPComp.sample Bool := rfl

/-- Uniform sampling at the code `unit` is uniform sampling of `Unit`. -/
@[simp] theorem sampleFin_unit (h : EcTy.unit.isFin = true) :
    EcTy.unit.sampleFin h = SPComp.sample Unit := rfl

/-- Uniform sampling at the code `fin n` is uniform sampling of `Fin n`. -/
@[simp] theorem sampleFin_fin (n : Nat) (hn : 0 < n) (h : (EcTy.fin n hn).isFin = true) :
    (EcTy.fin n hn).sampleFin h
      = @SPComp.sample (Fin n) inferInstance ⟨⟨0, hn⟩⟩ := rfl

/-! ## Distribution expressions

A distribution expression denotes an `SDistr` over the interpretation of its code,
against a local valuation. A binder is an `EcVarId`, and the sub-expression or
sub-distribution under it is evaluated in the valuation extended at that identity
by the value the enclosing distribution supplies. Since the identity carries the
binder's uniqueness stamp and a program variable's does not, extending at a binder
leaves the program variable of the binder's source name readable
(`Env.read_update_stamped`). -/

/-- The sub-distribution a distribution expression denotes against a local
valuation. -/
noncomputable def evalDistr : {t : EcTy} → EcDistr t → Env → CatCrypt.Prob.SDistr t.interp
  | _, .uniform t h, _ =>
      letI := t.fintypeOfIsFin h
      CatCrypt.Prob.SDistr.uniform t.interp
  | _, .point e, env => CatCrypt.Prob.SDistr.pure (evalExpr e env)
  | _, .map (a := a) d x e, env =>
      (evalDistr d env).bind fun v =>
        CatCrypt.Prob.SDistr.pure (evalExpr e (env.update x ⟨a, v⟩))
  | _, .cond (t := t) d x p, env =>
      NonUniform.condition (evalDistr d env)
        (fun v => evalExpr p (env.update x ⟨t, v⟩))
  | _, .letD (a := a) d x body, env =>
      (evalDistr d env).bind fun v => evalDistr body (env.update x ⟨a, v⟩)
  | _, .prod d₁ d₂, env => NonUniform.prod (evalDistr d₁ env) (evalDistr d₂ env)
  | _, .scale d, env => NonUniform.scale (evalDistr d env)
  | _, .restrict (t := t) d x p, env =>
      NonUniform.restrict (evalDistr d env)
        (fun v => evalExpr p (env.update x ⟨t, v⟩))
  | _, .ofExpr e, env => evalExpr e env

/-- The uniform distribution expression at a finite code denotes the uniform
sub-distribution on that code's interpretation. -/
@[simp] theorem evalDistr_uniform (t : EcTy) (h : t.isFin = true) (env : Env) :
    evalDistr (.uniform t h) env =
      letI := t.fintypeOfIsFin h
      CatCrypt.Prob.SDistr.uniform t.interp := rfl

/-- A point-mass distribution expression denotes the point mass at the
expression's value. -/
@[simp] theorem evalDistr_point {t : EcTy} (e : EcExpr t) (env : Env) :
    evalDistr (.point e) env = CatCrypt.Prob.SDistr.pure (evalExpr e env) := rfl

/-- A pushforward distribution expression denotes the pushforward of the
sub-distribution its argument denotes. -/
@[simp] theorem evalDistr_map {a b : EcTy} (d : EcDistr a) (x : EcVarId)
    (e : EcExpr b) (env : Env) :
    evalDistr (.map d x e) env =
      (evalDistr d env).bind fun v =>
        CatCrypt.Prob.SDistr.pure (evalExpr e (env.update x ⟨a, v⟩)) := rfl

/-- A conditioned distribution expression denotes the conditioning of the
sub-distribution its argument denotes on the predicate its body evaluates to. -/
@[simp] theorem evalDistr_cond {t : EcTy} (d : EcDistr t) (x : EcVarId)
    (p : EcExpr .bool) (env : Env) :
    evalDistr (.cond d x p) env =
      NonUniform.condition (evalDistr d env)
        (fun v => evalExpr p (env.update x ⟨t, v⟩)) := rfl

/-- A bind distribution expression denotes the `SDistr` bind of what its two
arguments denote, the second under the binder. -/
@[simp] theorem evalDistr_letD {a b : EcTy} (d : EcDistr a) (x : EcVarId)
    (body : EcDistr b) (env : Env) :
    evalDistr (.letD d x body) env =
      (evalDistr d env).bind fun v => evalDistr body (env.update x ⟨a, v⟩) := rfl

/-- A product distribution expression denotes the independent product of what its
two factors denote. -/
@[simp] theorem evalDistr_prod {a b : EcTy} (d₁ : EcDistr a) (d₂ : EcDistr b)
    (env : Env) :
    evalDistr (.prod d₁ d₂) env =
      NonUniform.prod (evalDistr d₁ env) (evalDistr d₂ env) := rfl

/-- A rescaled distribution expression denotes the rescaling of what its argument
denotes. -/
@[simp] theorem evalDistr_scale {t : EcTy} (d : EcDistr t) (env : Env) :
    evalDistr (.scale d) env = NonUniform.scale (evalDistr d env) := rfl

/-- A restricted distribution expression denotes the restriction of what its
argument denotes to the predicate its body evaluates to. -/
@[simp] theorem evalDistr_restrict {t : EcTy} (d : EcDistr t) (x : EcVarId)
    (p : EcExpr .bool) (env : Env) :
    evalDistr (.restrict d x p) env =
      NonUniform.restrict (evalDistr d env)
        (fun v => evalExpr p (env.update x ⟨t, v⟩)) := rfl

/-- A distribution read out of an expression denotes the expression's value:
the `distr` code's interpretation is `SDistr` itself. -/
@[simp] theorem evalDistr_ofExpr {t : EcTy} (e : EcExpr (.distr t)) (env : Env) :
    evalDistr (.ofExpr e) env = evalExpr e env := rfl

/-- Rescaling a restriction is conditioning: `EcDistr.cond` is the composite the
EasyCrypt definition `dcond d p = dscale (drestrict d p)` gives. -/
theorem evalDistr_scale_restrict {t : EcTy} (d : EcDistr t) (x : EcVarId)
    (p : EcExpr .bool) (env : Env) :
    evalDistr (.scale (.restrict d x p)) env = evalDistr (.cond d x p) env := rfl

/-- A bind at a point mass is a pushforward: `EcDistr.map` is the composite the
EasyCrypt definition `dmap d f = dlet d (dunit \o f)` gives. -/
theorem evalDistr_letD_point {a b : EcTy} (d : EcDistr a) (x : EcVarId)
    (e : EcExpr b) (env : Env) :
    evalDistr (.letD d x (.point e)) env = evalDistr (.map d x e) env := rfl

/-- Sampling from the uniform distribution expression is uniform sampling at the
code. `NonUniform.sampleFrom` at `SDistr.uniform` is `SPComp.sample`, so the
general sampler specialises to `EcTy.sampleFin` definitionally. -/
theorem sampleFrom_evalDistr_uniform (t : EcTy) (h : t.isFin = true) (env : Env) :
    NonUniform.sampleFrom (evalDistr (.uniform t h) env) = t.sampleFin h := rfl

/-! ## Statements -/

/-- The body of the argument-free procedure named `p` in the table `procs`, or
the empty block if `p` is not declared. -/
def procBody (procs : List (String × List EcStmt)) (p : String) : List EcStmt :=
  (procs.find? (fun kv => kv.1 = p)).elim [] Prod.snd

/-- Lower a statement block against a call-resolution environment `ρ`, an
argument-free procedure table `procs`, and a call-depth bound `fuel`, threading
the local valuation through `SPComp`. -/
noncomputable def lowerStmts (ρ : ProcEnv) (procs : List (String × List EcStmt)) :
    Nat → List EcStmt → Env → SPComp Env
  | _, [], env => SPComp.pure env
  | fuel, .assign t x e :: rest, env =>
      lowerStmts ρ procs fuel rest (env.update x ⟨t, evalExpr e env⟩)
  | fuel, .assignTuple t xs e :: rest, env =>
      lowerStmts ρ procs fuel rest (bindParams t xs (evalExpr e env) env)
  | fuel, .sample t x h :: rest, env =>
      SPComp.bind (t.sampleFin h)
        (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨t, v⟩))
  | fuel, .sampleD t x d :: rest, env =>
      SPComp.bind (NonUniform.sampleFrom (evalDistr d env))
        (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨t, v⟩))
  | fuel, .load g x :: rest, env =>
      SPComp.bind (SPComp.gget g.loc)
        (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨g.ty, v⟩))
  | fuel, .store g e :: rest, env =>
      SPComp.bind (SPComp.gset g.loc (evalExpr e env))
        (fun _ => lowerStmts ρ procs fuel rest env)
  | fuel, .ite c t f :: rest, env =>
      SPComp.bind
        (if evalCond c env then lowerStmts ρ procs fuel t env
         else lowerStmts ρ procs fuel f env)
        (fun env' => lowerStmts ρ procs fuel rest env')
  | fuel, .forN n body :: rest, env =>
      SPComp.bind
        (SPComp.foldM env (List.replicate n (fun e => lowerStmts ρ procs fuel body e)))
        (fun env' => lowerStmts ρ procs fuel rest env')
  | fuel, .callProc q s arg x :: rest, env =>
      SPComp.bind (ρ q s (evalExpr arg env))
        (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨s.res, v⟩))
  | fuel, .callProcTuple q s arg xs :: rest, env =>
      SPComp.bind (ρ q s (evalExpr arg env))
        (fun v => lowerStmts ρ procs fuel rest (bindParams s.res xs v env))
  | 0, .call _ :: rest, env => lowerStmts ρ procs 0 rest env
  | fuel + 1, .call p :: rest, env =>
      SPComp.bind (lowerStmts ρ procs fuel (procBody procs p) env)
        (fun env' => lowerStmts ρ procs (fuel + 1) rest env')
  termination_by fuel stmts _ => (fuel, sizeOf stmts)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; simp_wf; omega)
      | (simp_wf; omega)

@[simp] theorem lowerStmts_nil (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (env : Env) :
    lowerStmts ρ procs fuel [] env = SPComp.pure env := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_assign (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (t : EcTy) (x : String) (e : EcExpr t) (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.assign t x e :: rest) env
      = lowerStmts ρ procs fuel rest (env.update x ⟨t, evalExpr e env⟩) := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_assignTuple (ρ : ProcEnv)
    (procs : List (String × List EcStmt)) (fuel : Nat) (t : EcTy)
    (xs : List String) (e : EcExpr t) (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.assignTuple t xs e :: rest) env
      = lowerStmts ρ procs fuel rest (bindParams t xs (evalExpr e env) env) := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_sample (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (t : EcTy) (x : String) (h : t.isFin = true) (rest : List EcStmt)
    (env : Env) :
    lowerStmts ρ procs fuel (.sample t x h :: rest) env
      = SPComp.bind (t.sampleFin h)
          (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨t, v⟩)) := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_sampleD (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (t : EcTy) (x : String) (d : EcDistr t) (rest : List EcStmt)
    (env : Env) :
    lowerStmts ρ procs fuel (.sampleD t x d :: rest) env
      = SPComp.bind (NonUniform.sampleFrom (evalDistr d env))
          (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨t, v⟩)) := by
  simp [lowerStmts]

/-- The general sampling arm at the uniform distribution expression is the
uniform sampling arm. `EcStmt.sample` is therefore a special case of
`EcStmt.sampleD`, and an imported uniform sample lowers to the same `SPComp`
program either way. -/
theorem lowerStmts_sampleD_uniform (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (t : EcTy) (x : String) (h : t.isFin = true) (rest : List EcStmt)
    (env : Env) :
    lowerStmts ρ procs fuel (.sampleD t x (.uniform t h) :: rest) env
      = lowerStmts ρ procs fuel (.sample t x h :: rest) env := by
  rw [lowerStmts_sampleD, lowerStmts_sample, sampleFrom_evalDistr_uniform]

@[simp] theorem lowerStmts_load (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (g : EcGlobal) (x : String) (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.load g x :: rest) env
      = SPComp.bind (SPComp.gget g.loc)
          (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨g.ty, v⟩)) := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_store (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (g : EcGlobal) (e : EcExpr g.ty) (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.store g e :: rest) env
      = SPComp.bind (SPComp.gset g.loc (evalExpr e env))
          (fun _ => lowerStmts ρ procs fuel rest env) := by
  simp [lowerStmts]

/-- The lowering of a global read at a finite code, in the finite-typed
vocabulary: `SPComp.gget` at the global's cell is `SPComp.get` at the `Location`
that cell also is. -/
theorem lowerStmts_load_finLoc (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (g : EcGlobal) (hfin : g.ty.isFin = true) (x : String)
    (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.load g x :: rest) env
      = SPComp.bind (SPComp.get (g.finLoc hfin))
          (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨g.ty, v⟩)) := by
  funext hp
  simp only [lowerStmts_load, EcGlobal.loc_finLoc g hfin, SPComp.bind, SPComp.gget,
    SPComp.get, CatCrypt.Prob.SDistr.pure_bind, Heap.gget_ofLocation]

/-- The lowering of a global write at a finite code, in the finite-typed
vocabulary: `SPComp.gset` at the global's cell is `SPComp.set` at the `Location`
that cell also is. -/
theorem lowerStmts_store_finLoc (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (g : EcGlobal) (hfin : g.ty.isFin = true) (e : EcExpr g.ty)
    (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.store g e :: rest) env
      = SPComp.bind (SPComp.set (g.finLoc hfin) (evalExpr e env))
          (fun _ => lowerStmts ρ procs fuel rest env) := by
  rw [lowerStmts_store, show SPComp.gset g.loc (evalExpr e env)
      = SPComp.set (g.finLoc hfin) (evalExpr e env) from
    SPComp.gset_ofLocation (g.finLoc hfin) (evalExpr e env)]

@[simp] theorem lowerStmts_ite (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (c : EcExpr .bool) (t f rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.ite c t f :: rest) env
      = SPComp.bind
          (if evalCond c env then lowerStmts ρ procs fuel t env
           else lowerStmts ρ procs fuel f env)
          (fun env' => lowerStmts ρ procs fuel rest env') := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_forN (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (n : Nat) (body rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.forN n body :: rest) env
      = SPComp.bind
          (SPComp.foldM env (List.replicate n (fun e => lowerStmts ρ procs fuel body e)))
          (fun env' => lowerStmts ρ procs fuel rest env') := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_callProc (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (q : String) (s : EcSig) (arg : EcExpr s.arg) (x : String)
    (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.callProc q s arg x :: rest) env
      = SPComp.bind (ρ q s (evalExpr arg env))
          (fun v => lowerStmts ρ procs fuel rest (env.update x ⟨s.res, v⟩)) := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_callProcTuple (ρ : ProcEnv)
    (procs : List (String × List EcStmt)) (fuel : Nat) (q : String) (s : EcSig)
    (arg : EcExpr s.arg) (xs : List String) (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.callProcTuple q s arg xs :: rest) env
      = SPComp.bind (ρ q s (evalExpr arg env))
          (fun v => lowerStmts ρ procs fuel rest (bindParams s.res xs v env)) := by
  simp [lowerStmts]

@[simp] theorem lowerStmts_call_succ (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (p : String) (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs (fuel + 1) (.call p :: rest) env
      = SPComp.bind (lowerStmts ρ procs fuel (procBody procs p) env)
          (fun env' => lowerStmts ρ procs (fuel + 1) rest env') := by
  simp [lowerStmts]

theorem lowerStmts_call_zero (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (p : String) (rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs 0 (.call p :: rest) env = lowerStmts ρ procs 0 rest env := by
  simp [lowerStmts]

/-! ## Procedures, modules, functors, games -/

/-- Lower a procedure body at signature `s` to a function from the argument to
an `SPComp` computation of the result: bind each formal parameter to its
component of the argument, run the body, and evaluate the return expression on
the final valuation. -/
noncomputable def lowerProcAt (ρ : ProcEnv) (fuel : Nat) {s : EcSig} (pr : EcProcAt s) :
    s.arg.interp → SPComp s.res.interp :=
  fun a =>
    SPComp.bind
      (lowerStmts ρ [] fuel pr.body (bindParams s.arg pr.params a emptyEnv))
      (fun env => SPComp.pure (evalExpr pr.ret env))

/-- Lower a concrete module to a record of `SPComp` procedures over its
interface. The module's globals are shared through the heap: each procedure body
reads and writes the cells of the module's `EcGlobal`s. -/
noncomputable def lowerModule (ρ : ProcEnv) (fuel : Nat) (M : EcModule) :
    ModuleImpl M.interface where
  proc := fun p => lowerProcAt ρ fuel (M.procs p)

@[simp] theorem lowerModule_proc (ρ : ProcEnv) (fuel : Nat) (M : EcModule) (p : String) :
    (lowerModule ρ fuel M).proc p = lowerProcAt ρ fuel (M.procs p) := rfl

/-- Lower a functor to a Lean function on module records: the parameter module
is bound in the resolution environment under the functor's parameter prefix, and
the functor body is lowered against that environment. Functor application is
function application. -/
noncomputable def lowerFunctor (ρ : ProcEnv) (fuel : Nat) (F : EcFunctor)
    (X : ModuleImpl F.paramInterface) : ModuleImpl F.body.interface :=
  lowerModule (ρ.bindModule F.paramName X) fuel F.body

@[simp] theorem lowerFunctor_proc (ρ : ProcEnv) (fuel : Nat) (F : EcFunctor)
    (X : ModuleImpl F.paramInterface) (p : String) :
    (lowerFunctor ρ fuel F X).proc p
      = lowerProcAt (ρ.bindModule F.paramName X) fuel (F.body.procs p) := rfl

/-- Lower a functor whose body calls its parameter by the cross-paths the
exporter writes, which is the shape a decoded functor has. `lowerFunctor` is the
same lowering for a body that calls the parameter by `qualify`. -/
noncomputable def lowerFunctorX (ρ : ProcEnv) (fuel : Nat) (F : EcFunctor)
    (X : ModuleImpl F.paramInterface) : ModuleImpl F.body.interface :=
  lowerModule (ρ.bindModuleX F.paramName X) fuel F.body

@[simp] theorem lowerFunctorX_proc (ρ : ProcEnv) (fuel : Nat) (F : EcFunctor)
    (X : ModuleImpl F.paramInterface) (p : String) :
    (lowerFunctorX ρ fuel F X).proc p
      = lowerProcAt (ρ.bindModuleX F.paramName X) fuel (F.body.procs p) := rfl

/-- Lower a game to `SPComp Bool`: run the body from the initial valuation under
the resolution environment `ρ`, the game's argument-free procedure table and the
call-depth bound `fuel`, then return the game's result bit. -/
noncomputable def lowerGame (ρ : ProcEnv) (g : EcGame) (fuel : Nat := 0) : SPComp Bool :=
  SPComp.bind (lowerStmts ρ g.procs fuel g.body emptyEnv)
    (fun env => SPComp.pure (evalExpr g.ret env))

/-- Lower a game that calls no external module. -/
noncomputable def lowerClosedGame (g : EcGame) (fuel : Nat := 0) : SPComp Bool :=
  lowerGame ProcEnv.empty g fuel

/-- Lower a game parameterised by an abstract module bound at `advName`: the
result is a family of games indexed by the module parameter, which is the shape
an imported EasyCrypt experiment `Exp(A)` takes — a statement about it
quantifies over `A : ModuleImpl I`. -/
noncomputable def lowerGameWith (ρ : ProcEnv) (advName : String) {I : EcInterface}
    (g : EcGame) (fuel : Nat) (A : ModuleImpl I) : SPComp Bool :=
  lowerGame (ρ.bindModule advName A) g fuel

/-! ## Agreement with the hax loop-phase fold image

`iterateM f n a` is the canonical `n`-fold monadic iteration of `f`, threading the
accumulator: it returns `a` after zero steps and runs `f` once before recursing on
the remaining steps. This is the shape the hax `functionalizeLoops` phase produces
for a bounded `for` loop (`denoteForLoop'`): a bounded index recursion that runs
the body once per index and threads the accumulator. The importer emits the loop
as `SPComp.foldM env (List.replicate n step)`, and `foldM_replicate_eq_iterateM`
proves that fold equals `iterateM`, establishing that the direct lowering lands on
the same fold image. -/

/-- The canonical `n`-fold monadic iteration of a step `f`, threading the
accumulator through `SPComp`. `iterateM f 0 a = pure a`, and
`iterateM f (n+1) a = f a >>= iterateM f n`. -/
noncomputable def iterateM {α : Type} (f : α → SPComp α) : Nat → α → SPComp α
  | 0,     a => SPComp.pure a
  | n + 1, a => SPComp.bind (f a) (iterateM f n)

@[simp] theorem iterateM_zero {α : Type} (f : α → SPComp α) (a : α) :
    iterateM f 0 a = SPComp.pure a := rfl

@[simp] theorem iterateM_succ {α : Type} (f : α → SPComp α) (n : Nat) (a : α) :
    iterateM f (n + 1) a = SPComp.bind (f a) (iterateM f n) := rfl

/-- The importer's loop image `SPComp.foldM a (List.replicate n f)` equals the
canonical `n`-fold monadic iteration `iterateM f n a`. -/
theorem foldM_replicate_eq_iterateM {α : Type} (f : α → SPComp α) (n : Nat) (a : α) :
    SPComp.foldM a (List.replicate n f) = iterateM f n a := by
  induction n generalizing a <;> simp_all [List.replicate_succ, SPComp.foldM_cons]

/-- Fold-image agreement: the importer's `forN` lowering emits, for a bounded
loop over `n` iterations of the lowered `body`, the fold `SPComp.foldM` over
`n` copies of the loop step, and that fold equals the canonical `n`-fold monadic
iteration `iterateM` of the step. This is the shape the hax `functionalizeLoops`
phase targets for a `for` loop (`denoteForLoop'`, a bounded index recursion that
threads the accumulator through the body once per index): the importer's direct
lowering produces the same fold image, up to the `iterateM` bridge between the
`SPComp` target and the deterministic hax state monad. -/
theorem forN_lowering_agrees_hax_foldImage (ρ : ProcEnv)
    (procs : List (String × List EcStmt)) (fuel n : Nat) (body : List EcStmt) (env : Env) :
    SPComp.foldM env (List.replicate n (fun e => lowerStmts ρ procs fuel body e))
      = iterateM (fun e => lowerStmts ρ procs fuel body e) n env :=
  foldM_replicate_eq_iterateM _ n env

/-- The `forN` lowering unfolds to the canonical `n`-fold iteration of the loop
step, sequenced with the continuation. -/
theorem lowerStmts_forN_iterateM (ρ : ProcEnv) (procs : List (String × List EcStmt))
    (fuel : Nat) (n : Nat) (body rest : List EcStmt) (env : Env) :
    lowerStmts ρ procs fuel (.forN n body :: rest) env
      = SPComp.bind
          (iterateM (fun e => lowerStmts ρ procs fuel body e) n env)
          (fun env' => lowerStmts ρ procs fuel rest env') := by
  rw [lowerStmts_forN, forN_lowering_agrees_hax_foldImage]

end CatCrypt.Crypto.EasyCryptImport
