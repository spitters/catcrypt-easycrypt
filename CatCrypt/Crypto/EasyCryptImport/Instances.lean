/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Json
import CatCrypt.Crypto.EasyCryptImport.FormToProp

/-!
# EasyCrypt import: type-class instances

An EasyCrypt `instance ring with t` declaration names a type together with the
operators EasyCrypt's algebraic tactics resolve against it. This module decodes
that declaration and gives it an image built from the two pieces the importer
already has: the operators the declaration names are parameters, at the
signatures the declaration gives them, and the axioms EasyCrypt required of the
declaration are `EcForm` premises about those parameters.

## The image is a bundle, not a `Ring` instance

Declaring `instance : Ring t.interp` would postulate the ring laws for the
decoded operators at the carrier `Ty.lean` fixes. EasyCrypt's declaration is
backed by proofs that do not cross the exporter boundary, so nothing here
establishes those laws, and a postulate that fails at the carrier is a false
axiom. A bundle of premises leaves the obligation with whoever instantiates it:
`EcInstance.satisfiedBy` is a proposition about a realization, and a Mathlib
`Ring` instance derived at a realization that meets it is a theorem someone
proved.

## Which laws attach is determined by the payload

EasyCrypt derives a declaration's obligations from exactly which optional
operators it named, in `EcAlgTactic.Axioms.ring_axioms`: the core axioms of the
`rkind`, then `oppr_id` for a boolean ring that names `opp`, then `expr0` and
`exprS` when `exp` is named, the four `ofint` laws when the embedding is an
`Embed`, `subrE` when `sub` is named, and `Cn_eq0` / `Cp_idp` for the components
a `Modulus` bounds. A field adds `mulrV` and `exprN`, and `divrE` when `div` is
named. `EcRingOps.obligations` and `EcInstanceBody.obligations` are that
selection, and each law's statement is the corresponding axiom of EasyCrypt's
`theories/tactics/AlgTactic.ec` theory `Requires` with the declaration's own
operator paths in place of `Requires`'s abstract ones — the substitution
EasyCrypt itself performs. A law the payload does not oblige is not in the list,
because importing it would state something stronger than the source.

## Two operators the term fragment cannot spell

`ofintN` and `exprN` read `ofint (-n)` and `expr x (-n)`, at the integer negation
`EcTerm` carries. `ofintN_iff` and `exprN_iff` are each law at a realization.

## `General` bundles nothing

A `General` instance carries a class path and no operators, so there is no
operator to parametrise and no law to attach. `EcInstanceBody.obligations`
rejects it with the class path in the message, and `EcInstance.satisfiedBy` is
`False` there: a general instance has no realization to satisfy, and an empty
bundle would read as coverage.

## Main definitions

* `EcRingOps`, `EcRingEmbed`, `EcRingKind`, `EcInstanceBody`, `EcInstance`: the
  decoded `Th_instance` payload of schema version `schemaVersion`.
* `decodeThInstance`: the decode from the exporter's node into `EcInstance`.
* `EcRingOps.nulSig`, `.unSig`, `.binSig`, `.expSig`, `.embSig`: the signature
  the declaration gives each operator, which is the shape `DecodeTables.absOpPaths`
  binds an abstract operator at and the shape `EcTerm.opApp` reads it at.
* `EcRingOps.obligations`, `EcInstanceBody.obligations`, `EcInstance.obligations`:
  the named law forms the declaration is obliged to, or a rejection.
* `EcInstance.opSigs`: the operator paths the declaration names, each at its
  signature.
* `EcInstance.satisfiedBy`, `lawsHold`: the proposition that a realization of the
  operators meets the obligations.
* `EcInstance.underLaws`: a goal over the carrier, closed over the operators and
  under the obligations as premises.

## Main results

* `addr0_iff`, `addrA_iff`, `addrC_iff`, `addrN_iff`, `addrK_iff`, `onerNeq0_iff`,
  `opprId_iff`, `mulr1_iff`, `mulrA_iff`, `mulrC_iff`, `mulrDl_iff`, `mulrK_iff`,
  `expr0_iff`, `exprS_iff`, `ofint0_iff`, `ofint1_iff`, `ofintS_iff`,
  `ofintN_iff`, `subrE_iff`, `mulrV_iff`, `exprN_iff`, `divrE_iff`,
  `CnEq0_iff`, `CpIdp_iff`: each law form, at a realization, is the expected
  statement about that realization's operators.
* `general_obligations_isError`: a general instance obliges no law.
* `not_satisfiedBy_of_error`: an instance with no image has no satisfying
  realization, so a rejection is not an empty bundle.
* `stdRingInt_obligation_names`, `stdRingBool_obligation_names`: the laws the two
  declarations of `algebra/StdRing.ec` are obliged to, which are the `proof`
  clauses those declarations carry.
* `stdRingInt_opSigs`: each operator of the integer ring at the signature the
  declaration gives it.
* `stdRingInt_underLaws_opsOf`, `stdRingBool_underLaws_opsOf`: a goal stated
  under a declaration's obligations reads no operator it does not bind.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)

/-! ## The payload -/

/-- The map from the integers a ring declaration carries: the identity at the
integer type, a named embedding operator, or none. -/
inductive EcRingEmbed where
  /-- `{"kind": "Direct"}`: the type is `int` and the embedding is the identity. -/
  | direct
  /-- `{"kind": "Embed", "path": p}`: the declaration named the operator `p`. -/
  | embed (path : String)
  /-- `{"kind": "Default"}`: the declaration named no embedding and the type is
  not `int`. -/
  | dflt
  deriving DecidableEq, Repr, Inhabited

/-- The coefficient structure a ring declaration carries. -/
inductive EcRingKind where
  /-- A `bring` declaration. -/
  | boolean
  /-- An unconstrained `ring` or `field` declaration. -/
  | integer
  /-- A `ring c p` declaration, bounding the coefficients and the exponents; a
  `none` component is a bound the declaration left open. -/
  | modulus (coeff power : Option Int)
  deriving DecidableEq, Repr, Inhabited

/-- The operator set a `Ring` or `Field` instance carries. -/
structure EcRingOps where
  /-- The `as` clause's name. -/
  name : Option String
  /-- The type the operators are over. -/
  ty : EcTy
  /-- The zero. -/
  zero : String
  /-- The one. -/
  one : String
  /-- The addition. -/
  add : String
  /-- The opposite, when the declaration named one. -/
  opp : Option String
  /-- The multiplication. -/
  mul : String
  /-- The integer exponentiation, when the declaration named one. -/
  exp : Option String
  /-- The subtraction, when the declaration named one. -/
  sub : Option String
  /-- The map from the integers. -/
  embed : EcRingEmbed
  /-- The coefficient structure. -/
  rkind : EcRingKind
  deriving DecidableEq, Repr

/-- What a `Th_instance` item declares the type to be an instance of. -/
inductive EcInstanceBody where
  /-- `{"kind": "Ring", …}`. -/
  | ring (r : EcRingOps)
  /-- `{"kind": "Field", …}`, whose inversion is always named and whose division
  is named or not. -/
  | field (r : EcRingOps) (inv : String) (div : Option String)
  /-- `{"kind": "General", "path": p}`: the declared type class `p`, and no
  operators. -/
  | general (path : String)
  deriving DecidableEq, Repr

/-- Where a declaration is visible from. -/
inductive EcLocality where
  /-- Visible outside the enclosing section. -/
  | global
  /-- Visible inside the enclosing section only. -/
  | «local»
  deriving DecidableEq, Repr, Inhabited

/-- A decoded `Th_instance` item: the type parameters it holds under, the type,
its visibility, and what it declares the type to be an instance of. -/
structure EcInstance where
  /-- Each type parameter's name and uniqueness stamp. -/
  tparams : List (String × Nat)
  /-- The type the instance is declared for. -/
  ty : EcTy
  /-- Where the declaration is visible from. -/
  locality : EcLocality
  /-- What the type is declared to be an instance of. -/
  body : EcInstanceBody
  deriving DecidableEq, Repr

/-! ## The decode

Every field is read: a missing one is a decode error rather than a default, and
an optional operator arrives as an explicit `null` whose absence is information
(`EcRingOps.obligations` reads it). -/

/-- The value of a field that is either a string or `null`. -/
def getNullableStr (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .ok .null => .ok none
  | .ok (.str s) => .ok (some s)
  | .ok v => fail s!"field '{k}' is neither a path nor null: {v.compress}"
  | .error _ => fail s!"missing field '{k}' in {j.compress}"

/-- The value of a field holding a decimal integer as a string, or `null`. -/
def getNullableDecimal (j : Json) (k : String) : Except String (Option Int) := do
  match ← getNullableStr j k with
  | none => .ok none
  | some s =>
    match s.toInt? with
    | some v => .ok (some v)
    | none => fail s!"field '{k}' is not a decimal integer: '{s}'"

/-- The embedding node of a ring payload. -/
def decodeRingEmbed (j : Json) : Except String EcRingEmbed := do
  match ← getStr j "kind" with
  | "Direct" => .ok .direct
  | "Default" => .ok .dflt
  | "Embed" => .ok (.embed (← getStr j "path"))
  | k => fail s!"unknown embedding kind '{k}' in {j.compress}"

/-- The coefficient-structure node of a ring payload. -/
def decodeRingKind (j : Json) : Except String EcRingKind := do
  match ← getStr j "kind" with
  | "Boolean" => .ok .boolean
  | "Integer" => .ok .integer
  | "Modulus" =>
      .ok (.modulus (← getNullableDecimal j "coeff") (← getNullableDecimal j "power"))
  | k => fail s!"unknown ring kind '{k}' in {j.compress}"

/-- The operator set of a `Ring` or `Field` payload. -/
def decodeRingOps (T : DecodeTables) (j : Json) : Except String EcRingOps := do
  let name ← getNullableStr j "name"
  let ty ← decodeTyField T j "ty"
  let zero ← getStr j "zero"
  let one ← getStr j "one"
  let add ← getStr j "add"
  let opp ← getNullableStr j "opp"
  let mul ← getStr j "mul"
  let exp ← getNullableStr j "exp"
  let sub ← getNullableStr j "sub"
  let embed ← decodeRingEmbed (← getObj j "embed")
  let rkind ← decodeRingKind (← getObj j "rkind")
  .ok { name, ty, zero, one, add, opp, mul, exp, sub, embed, rkind }

/-- The `instance` node of a `Th_instance` item. -/
def decodeInstanceBody (T : DecodeTables) (j : Json) :
    Except String EcInstanceBody := do
  match ← getStr j "kind" with
  | "Ring" => .ok (.ring (← decodeRingOps T (← getObj j "ring")))
  | "Field" =>
      .ok (.field (← decodeRingOps T (← getObj j "ring")) (← getStr j "inv")
        (← getNullableStr j "div"))
  | "General" => .ok (.general (← getStr j "path"))
  | k => fail s!"unknown instance kind '{k}' in {j.compress}"

/-- The `locality` field of a declaration. -/
def decodeLocality (j : Json) : Except String EcLocality := do
  match ← getStr j "locality" with
  | "global" => .ok .global
  | "local" => .ok .«local»
  | l => fail s!"unknown locality '{l}' in {j.compress}"

/-- One type parameter of an instance: its name and its uniqueness stamp, which
is what matches it to its occurrences in the type. -/
def decodeInstanceTparam (j : Json) : Except String (String × Nat) := do
  .ok (← getStr j "name", ← getNat j "stamp")

/-- A `Th_instance` item. -/
def decodeThInstance (T : DecodeTables) (j : Json) : Except String EcInstance := do
  let kind ← getStr j "kind"
  if kind ≠ "Th_instance" then
    fail s!"expected a 'Th_instance' item, got '{kind}' in {j.compress}"
  else
    let tps ← getArr j "tparams"
    let tparams ← tps.toList.mapM decodeInstanceTparam
    .ok { tparams,
          ty := ← decodeTyField T j "ty",
          locality := ← decodeLocality j,
          body := ← decodeInstanceBody T (← getObj j "instance") }

/-! ## The integer side of a law

Several laws quantify over an integer, bound it below, or add one to it. Those
integer sub-terms are `EcTerm` nodes: the laws are statements in the logic, not
program expressions. -/

/-- The integer logical variable `n`. -/
def ringVarN : EcTerm .int := .var .int "n"

/-- `-n`. -/
def ringVarNeg : EcTerm .int := .intOpp (.var .int "n")

/-- `n + 1`. -/
def ringVarNSucc : EcTerm .int :=
  .intAdd (.var .int "n") (.lit (t := .int) (1 : Int))

/-- `0 <= n`. -/
def ringNNonneg : EcForm :=
  .holds (.intLe (.lit (t := .int) (0 : Int)) (.var .int "n"))


namespace EcRingOps

variable (r : EcRingOps)

/-! ## The signature each operator is read at

These are the signatures `DecodeTables.withAbstractOp` registers an abstract
declaration at, so an operator of an instance and the same operator read by a
decoded statement are the same parameter. They are reducible: a law's proof
rewrites under `EcSig.arg` of one of them, which needs the projection to reduce
to the carrier. -/

/-- The signature of a nullary operator: the zero and the one. -/
@[reducible] def nulSig : EcSig := ⟨.unit, r.ty⟩

/-- The signature of a one-argument operator: the opposite, the inverse. -/
@[reducible] def unSig : EcSig := ⟨r.ty, r.ty⟩

/-- The signature of a two-argument operator: the addition, the multiplication,
the subtraction, the division. -/
@[reducible] def binSig : EcSig := ⟨.prod r.ty r.ty, r.ty⟩

/-- The signature of the integer exponentiation. -/
@[reducible] def expSig : EcSig := ⟨.prod r.ty .int, r.ty⟩

/-- The signature of the map from the integers. -/
@[reducible] def embSig : EcSig := ⟨.int, r.ty⟩

/-- The operator paths the declaration names, each at the signature the
declaration gives it, in the order the payload lists them. This is the shape
`DecodeTables.absOpPaths` holds, and an operator absent from the payload is
absent here. -/
def opSigs : List (String × EcSig) :=
  [(r.zero, r.nulSig), (r.one, r.nulSig), (r.add, r.binSig), (r.mul, r.binSig)]
    ++ (match r.opp with | some p => [(p, r.unSig)] | none => [])
    ++ (match r.sub with | some p => [(p, r.binSig)] | none => [])
    ++ (match r.exp with | some p => [(p, r.expSig)] | none => [])
    ++ (match r.embed with | .embed p => [(p, r.embSig)] | _ => [])

/-! ## Terms over the operators -/

/-- The term reading the nullary operator declared at `p`. -/
def cstT (p : String) : EcTerm r.ty := .opApp p r.nulSig (.lit (t := .unit) ())

/-- The term applying the one-argument operator declared at `p`. -/
def unT (p : String) (x : EcTerm r.ty) : EcTerm r.ty := .opApp p r.unSig x

/-- The term applying the two-argument operator declared at `p`, whose argument
is the pair of the two operands. -/
def binT (p : String) (x y : EcTerm r.ty) : EcTerm r.ty := .opApp p r.binSig (.pair x y)

/-- The term raising `x` to the integer `n` through the operator declared at
`p`. -/
def expT (p : String) (x : EcTerm r.ty) (n : EcTerm .int) : EcTerm r.ty :=
  .opApp p r.expSig (.pair x n)

/-- The term embedding the integer `n` through the operator declared at `p`. -/
def embT (p : String) (n : EcTerm .int) : EcTerm r.ty := .opApp p r.embSig n

/-- The logical variable `x` at the carrier. -/
def varX : EcTerm r.ty := .var r.ty "x"

/-- The logical variable `y` at the carrier. -/
def varY : EcTerm r.ty := .var r.ty "y"

/-- The logical variable `z` at the carrier. -/
def varZ : EcTerm r.ty := .var r.ty "z"

/-! ## The law forms

Each is the `AlgTactic.Requires` axiom of its name with the declaration's own
operator paths in place of `Requires`'s abstract ones. -/

/-- `oner_neq0`: `1 <> 0`. -/
def onerNeq0Form : EcForm := .not (.eqT (r.cstT r.one) (r.cstT r.zero))

/-- `addr0`: `forall x, x + 0 = x`. -/
def addr0Form : EcForm :=
  .allTy r.ty "x" (.eqT (r.binT r.add r.varX (r.cstT r.zero)) r.varX)

/-- `addrA`: `forall x y z, x + (y + z) = (x + y) + z`. -/
def addrAForm : EcForm :=
  .allTy r.ty "x" (.allTy r.ty "y" (.allTy r.ty "z"
    (.eqT (r.binT r.add r.varX (r.binT r.add r.varY r.varZ))
      (r.binT r.add (r.binT r.add r.varX r.varY) r.varZ))))

/-- `addrC`: `forall x y, x + y = y + x`. -/
def addrCForm : EcForm :=
  .allTy r.ty "x" (.allTy r.ty "y"
    (.eqT (r.binT r.add r.varX r.varY) (r.binT r.add r.varY r.varX)))

/-- `addrN`: `forall x, x + (-x) = 0`, at the opposite declared at `opp`. -/
def addrNForm (opp : String) : EcForm :=
  .allTy r.ty "x" (.eqT (r.binT r.add r.varX (r.unT opp r.varX)) (r.cstT r.zero))

/-- `addrK`: `forall x, x + x = 0`, the boolean ring's replacement for
`addrN`. -/
def addrKForm : EcForm :=
  .allTy r.ty "x" (.eqT (r.binT r.add r.varX r.varX) (r.cstT r.zero))

/-- `oppr_id`: `forall x, -x = x`, at the opposite declared at `opp`. -/
def opprIdForm (opp : String) : EcForm :=
  .allTy r.ty "x" (.eqT (r.unT opp r.varX) r.varX)

/-- `mulr1`: `forall x, x * 1 = x`. -/
def mulr1Form : EcForm :=
  .allTy r.ty "x" (.eqT (r.binT r.mul r.varX (r.cstT r.one)) r.varX)

/-- `mulrA`: `forall x y z, x * (y * z) = (x * y) * z`. -/
def mulrAForm : EcForm :=
  .allTy r.ty "x" (.allTy r.ty "y" (.allTy r.ty "z"
    (.eqT (r.binT r.mul r.varX (r.binT r.mul r.varY r.varZ))
      (r.binT r.mul (r.binT r.mul r.varX r.varY) r.varZ))))

/-- `mulrC`: `forall x y, x * y = y * x`. -/
def mulrCForm : EcForm :=
  .allTy r.ty "x" (.allTy r.ty "y"
    (.eqT (r.binT r.mul r.varX r.varY) (r.binT r.mul r.varY r.varX)))

/-- `mulrDl`: `forall x y z, (x + y) * z = x * z + y * z`. -/
def mulrDlForm : EcForm :=
  .allTy r.ty "x" (.allTy r.ty "y" (.allTy r.ty "z"
    (.eqT (r.binT r.mul (r.binT r.add r.varX r.varY) r.varZ)
      (r.binT r.add (r.binT r.mul r.varX r.varZ) (r.binT r.mul r.varY r.varZ)))))

/-- `mulrK`: `forall x, x * x = x`, the boolean ring's idempotence. -/
def mulrKForm : EcForm :=
  .allTy r.ty "x" (.eqT (r.binT r.mul r.varX r.varX) r.varX)

/-- `expr0`: `forall x, x ^ 0 = 1`, at the exponentiation declared at `e`. -/
def expr0Form (e : String) : EcForm :=
  .allTy r.ty "x" (.eqT (r.expT e r.varX (.lit (t := .int) (0 : Int))) (r.cstT r.one))

/-- `exprS`: `forall x n, 0 <= n => x ^ (n + 1) = x * x ^ n`. -/
def exprSForm (e : String) : EcForm :=
  .allTy r.ty "x" (.allTy .int "n"
    (.imp ringNNonneg
      (.eqT (r.expT e r.varX ringVarNSucc)
        (r.binT r.mul r.varX (r.expT e r.varX ringVarN)))))

/-- `ofint0`: `ofint 0 = 0`, at the embedding declared at `emb`. -/
def ofint0Form (emb : String) : EcForm :=
  .eqT (r.embT emb (.lit (t := .int) (0 : Int))) (r.cstT r.zero)

/-- `ofint1`: `ofint 1 = 1`. -/
def ofint1Form (emb : String) : EcForm :=
  .eqT (r.embT emb (.lit (t := .int) (1 : Int))) (r.cstT r.one)

/-- `ofintS`: `forall n, 0 <= n => ofint (n + 1) = 1 + ofint n`. -/
def ofintSForm (emb : String) : EcForm :=
  .allTy .int "n"
    (.imp ringNNonneg
      (.eqT (r.embT emb ringVarNSucc) (r.binT r.add (r.cstT r.one) (r.embT emb ringVarN))))

/-- `ofintN`: `forall n, ofint (-n) = - ofint n`. -/
def ofintNForm (emb opp : String) : EcForm :=
  .allTy .int "n"
    (.eqT (r.embT emb ringVarNeg) (r.unT opp (r.embT emb ringVarN)))

/-- `subrE`: `forall x y, x - y = x + (-y)`, at the subtraction declared at
`sub`. -/
def subrEForm (sub opp : String) : EcForm :=
  .allTy r.ty "x" (.allTy r.ty "y"
    (.eqT (r.binT sub r.varX r.varY) (r.binT r.add r.varX (r.unT opp r.varY))))

/-- `mulrV`: `forall x, x <> 0 => x * x^-1 = 1`, at the inverse declared at
`inv`. -/
def mulrVForm (inv : String) : EcForm :=
  .allTy r.ty "x"
    (.imp (.not (.eqT r.varX (r.cstT r.zero)))
      (.eqT (r.binT r.mul r.varX (r.unT inv r.varX)) (r.cstT r.one)))

/-- `exprN`: `forall x n, 0 <= n => x ^ (-n) = (x ^ n)^-1`. -/
def exprNForm (e inv : String) : EcForm :=
  .allTy r.ty "x" (.allTy .int "n"
    (.imp ringNNonneg
      (.eqT (r.expT e r.varX ringVarNeg) (r.unT inv (r.expT e r.varX ringVarN)))))

/-- `divrE`: `forall x y, x / y = x * y^-1`, at the division declared at
`div`. -/
def divrEForm (div inv : String) : EcForm :=
  .allTy r.ty "x" (.allTy r.ty "y"
    (.eqT (r.binT div r.varX r.varY) (r.binT r.mul r.varX (r.unT inv r.varY))))

/-- `Cn_eq0`: `ofint Cn = 0`, at the coefficient bound `c`. -/
def CnEq0Form (emb : String) (c : Int) : EcForm :=
  .eqT (r.embT emb (.lit (t := .int) c)) (r.cstT r.zero)

/-- `Cp_idp`: `forall x, x ^ Cp = x`, at the exponent bound `p`. -/
def CpIdpForm (e : String) (p : Int) : EcForm :=
  .allTy r.ty "x" (.eqT (r.expT e r.varX (.lit (t := .int) p)) r.varX)

/-! ## The obligations the declaration carries -/

/-- The core axioms of the coefficient structure: `EcAlgTactic.Axioms.core` at an
integer or modulus kind, `core_bool` at a boolean one. A non-boolean declaration
that names no opposite has no `addrN` to state, and EasyCrypt requires the
opposite of one, so the payload is rejected rather than given a shorter list. -/
def coreObligations : Except String (List (String × EcForm)) :=
  match r.rkind with
  | .boolean =>
      .ok [("oner_neq0", r.onerNeq0Form), ("addr0", r.addr0Form),
           ("addrA", r.addrAForm), ("addrC", r.addrCForm),
           ("addrK", r.addrKForm), ("mulrK", r.mulrKForm),
           ("mulr1", r.mulr1Form), ("mulrA", r.mulrAForm),
           ("mulrC", r.mulrCForm), ("mulrDl", r.mulrDlForm)]
  | _ =>
    match r.opp with
    | some opp =>
        .ok [("oner_neq0", r.onerNeq0Form), ("addr0", r.addr0Form),
             ("addrA", r.addrAForm), ("addrC", r.addrCForm),
             ("addrN", r.addrNForm opp),
             ("mulr1", r.mulr1Form), ("mulrA", r.mulrAForm),
             ("mulrC", r.mulrCForm), ("mulrDl", r.mulrDlForm)]
    | none =>
        fail "a ring declaration outside the boolean kind names an opposite, and \
          this payload names none: 'addrN' has no statement"

/-- The named laws the declaration is obliged to, in the order
`EcAlgTactic.Axioms.ring_axioms` produces them. -/
def obligations : Except String (List (String × EcForm)) := do
  let axcore ← r.coreObligations
  let axopp : List (String × EcForm) :=
    match r.rkind, r.opp with
    | .boolean, some opp => [("oppr_id", r.opprIdForm opp)]
    | _, _ => []
  let axexp : List (String × EcForm) :=
    match r.exp with
    | some e => [("expr0", r.expr0Form e), ("exprS", r.exprSForm e)]
    | none => []
  let axint ←
    match r.embed with
    | .embed emb =>
      match r.opp with
      | some opp =>
          .ok [("ofint0", r.ofint0Form emb), ("ofint1", r.ofint1Form emb),
               ("ofintS", r.ofintSForm emb), ("ofintN", r.ofintNForm emb opp)]
      | none =>
          fail "the embedding's laws name the opposite, and this payload names \
            none: 'ofintN' has no statement"
    | _ => .ok []
  let axsub ←
    match r.sub, r.opp with
    | some sub, some opp => .ok [("subrE", r.subrEForm sub opp)]
    | some _, none =>
        fail "the subtraction's law names the opposite, and this payload names \
          none: 'subrE' has no statement"
    | none, _ => .ok []
  let axCnp ←
    match r.rkind with
    | .modulus c p =>
      match r.embed with
      | .embed emb =>
          .ok ((match c with
                | some c => [("Cn_eq0", r.CnEq0Form emb c)]
                | none => [])
            ++ (match p, r.exp with
                | some p, some e => [("Cp_idp", r.CpIdpForm e p)]
                | _, _ => []))
      | _ =>
          fail "a modulus declaration's coefficient law names the embedding, and \
            this payload names none: 'Cn_eq0' has no statement"
    | _ => .ok []
  .ok (axcore ++ axopp ++ axexp ++ axint ++ axsub ++ axCnp)

end EcRingOps

/-- The named laws a `Ring` or `Field` declaration is obliged to, in the order
`EcAlgTactic.Axioms.ring_axioms` and `field_axioms` produce them. A `General`
instance carries a class path and no operators, so there is nothing to bundle and
the class is named in the rejection. -/
def EcInstanceBody.obligations : EcInstanceBody → Except String (List (String × EcForm))
  | .ring r => r.obligations
  | .field r inv div => do
      let axring ← r.obligations
      let axcore ←
        match r.exp with
        | some e => .ok [("mulrV", r.mulrVForm inv), ("exprN", r.exprNForm e inv)]
        | none =>
            fail "a field's laws name the exponentiation, and this payload names \
              none: 'exprN' has no statement"
      let axdiv : List (String × EcForm) :=
        match div with
        | some d => [("divrE", r.divrEForm d inv)]
        | none => []
      .ok (axring ++ axcore ++ axdiv)
  | .general p =>
      fail s!"the instance of the type class '{p}' names a class and no \
        operators, so it obliges no law: a general instance has no image here \
        until the class has one"

/-- The operator paths a declaration names, each at its signature. -/
def EcInstanceBody.opSigs : EcInstanceBody → List (String × EcSig)
  | .ring r => r.opSigs
  | .field r inv div =>
      r.opSigs ++ [(inv, r.unSig)]
        ++ (match div with | some d => [(d, r.binSig)] | none => [])
  | .general _ => []

/-- The named laws the instance is obliged to. An instance under type parameters
is rejected: the operators' signatures would name the parameter, and a law form
is at a ground carrier. A payload whose two copies of the type disagree is
rejected too. -/
def EcInstance.obligations (i : EcInstance) : Except String (List (String × EcForm)) :=
  match i.tparams with
  | _ :: _ =>
      fail "an instance under type parameters has no image: the operators' \
        signatures would name the parameter"
  | [] =>
    match i.body with
    | .ring r =>
        if r.ty = i.ty then i.body.obligations
        else fail "the ring's type and the instance's type disagree"
    | .field r _ _ =>
        if r.ty = i.ty then i.body.obligations
        else fail "the ring's type and the instance's type disagree"
    | .general _ => i.body.obligations

/-- The operator paths the instance names, each at its signature. -/
def EcInstance.opSigs (i : EcInstance) : List (String × EcSig) := i.body.opSigs

/-! ## What the bundle says about a realization -/

/-- Every law of the list holds at the realization `ρ` of the operators. -/
noncomputable def lawsHold (ρ : OpEnv) (laws : List (String × EcForm)) : Prop :=
  ∀ nf ∈ laws, importedPropWithOps ProcEnv.empty ρ nf.2

/-- The realization `ρ` of the instance's operators meets the obligations the
declaration carries. An instance with no image has no satisfying realization,
which is what keeps a rejection from reading as an empty bundle. -/
noncomputable def EcInstance.satisfiedBy (i : EcInstance) (ρ : OpEnv) : Prop :=
  match i.obligations with
  | .ok laws => lawsHold ρ laws
  | .error _ => False

/-- A goal over the carrier as a statement of the theory the instance belongs to:
the obligations as premises, and one binder per operator the goal and the
premises read. `EcForm.opsOf` of the result is empty, so no operator resolves in
the ambient environment. -/
def EcInstance.underLaws (i : EcInstance) (goal : EcForm) : Except String EcForm :=
  i.obligations.map (fun laws => EcForm.assembleStatement (laws.map Prod.snd) goal)

/-! ## What a law says about a realization

A realization is an `OpEnv`, and these are its operators read at the signatures
the declaration gives them. Each `_iff` below is one law's content at a
realization, which is what a `Laws` field carries and what an instantiation has
to discharge. -/

namespace EcRingOps

variable (r : EcRingOps)

/-- The value the realization `ρ` gives the nullary operator declared at `p`. -/
def cstV (ρ : OpEnv) (p : String) : r.ty.interp := ρ p r.nulSig ()

/-- The function the realization `ρ` gives the one-argument operator at `p`. -/
def unV (ρ : OpEnv) (p : String) (x : r.ty.interp) : r.ty.interp := ρ p r.unSig x

/-- The function the realization `ρ` gives the two-argument operator at `p`. -/
def binV (ρ : OpEnv) (p : String) (x y : r.ty.interp) : r.ty.interp :=
  ρ p r.binSig (x, y)

/-- The function the realization `ρ` gives the exponentiation at `p`. -/
def expV (ρ : OpEnv) (p : String) (x : r.ty.interp) (n : Int) : r.ty.interp :=
  ρ p r.expSig (x, n)

/-- The function the realization `ρ` gives the embedding at `p`. -/
def embV (ρ : OpEnv) (p : String) (n : Int) : r.ty.interp := ρ p r.embSig n

end EcRingOps

/-- A literal term evaluates to the value it carries. -/
@[simp] theorem evalTerm_lit {t : EcTy} (v : t.interp) (ρ : FormEnv) :
    evalTerm (.lit v) ρ = v := rfl

@[simp] theorem evalTerm_cstT (r : EcRingOps) (p : String) (ρ : FormEnv) :
    evalTerm (r.cstT p) ρ = ρ.ops p r.nulSig () := rfl

@[simp] theorem evalTerm_unT (r : EcRingOps) (p : String) (x : EcTerm r.ty)
    (ρ : FormEnv) : evalTerm (r.unT p x) ρ = ρ.ops p r.unSig (evalTerm x ρ) := rfl

@[simp] theorem evalTerm_binT (r : EcRingOps) (p : String) (x y : EcTerm r.ty)
    (ρ : FormEnv) :
    evalTerm (r.binT p x y) ρ = ρ.ops p r.binSig (evalTerm x ρ, evalTerm y ρ) := rfl

@[simp] theorem evalTerm_expT (r : EcRingOps) (p : String) (x : EcTerm r.ty)
    (n : EcTerm .int) (ρ : FormEnv) :
    evalTerm (r.expT p x n) ρ = ρ.ops p r.expSig (evalTerm x ρ, evalTerm n ρ) := rfl

@[simp] theorem evalTerm_embT (r : EcRingOps) (p : String) (n : EcTerm .int)
    (ρ : FormEnv) : evalTerm (r.embT p n) ρ = ρ.ops p r.embSig (evalTerm n ρ) := rfl

/-! ### Reading a variable past a later binder

The laws bind up to three variables, and the inner binders leave the outer ones
readable because their names differ. -/

/-- Reading a variable past the binder of a different name. -/
private theorem read_past (env : Env) (t u : EcTy) (x y : String) (v : u.interp)
    (h : EcVarId.ofName y ≠ EcVarId.ofName x) :
    (env.update (EcVarId.ofName x) ⟨u, v⟩).read t (EcVarId.ofName y)
      = env.read t (EcVarId.ofName y) :=
  Env.read_update_ne _ _ _ _ _ h

@[local simp] private theorem read_x_past_y (env : Env) (t u : EcTy) (v : u.interp) :
    (env.update (EcVarId.ofName "y") ⟨u, v⟩).read t (EcVarId.ofName "x")
      = env.read t (EcVarId.ofName "x") := read_past _ _ _ _ _ _ (by decide)

@[local simp] private theorem read_x_past_z (env : Env) (t u : EcTy) (v : u.interp) :
    (env.update (EcVarId.ofName "z") ⟨u, v⟩).read t (EcVarId.ofName "x")
      = env.read t (EcVarId.ofName "x") := read_past _ _ _ _ _ _ (by decide)

@[local simp] private theorem read_x_past_n (env : Env) (t u : EcTy) (v : u.interp) :
    (env.update (EcVarId.ofName "n") ⟨u, v⟩).read t (EcVarId.ofName "x")
      = env.read t (EcVarId.ofName "x") := read_past _ _ _ _ _ _ (by decide)

@[local simp] private theorem read_x_past_m (env : Env) (t u : EcTy) (v : u.interp) :
    (env.update (EcVarId.ofName "m") ⟨u, v⟩).read t (EcVarId.ofName "x")
      = env.read t (EcVarId.ofName "x") := read_past _ _ _ _ _ _ (by decide)

@[local simp] private theorem read_y_past_z (env : Env) (t u : EcTy) (v : u.interp) :
    (env.update (EcVarId.ofName "z") ⟨u, v⟩).read t (EcVarId.ofName "y")
      = env.read t (EcVarId.ofName "y") := read_past _ _ _ _ _ _ (by decide)

@[local simp] private theorem read_n_past_m (env : Env) (t u : EcTy) (v : u.interp) :
    (env.update (EcVarId.ofName "m") ⟨u, v⟩).read t (EcVarId.ofName "n")
      = env.read t (EcVarId.ofName "n") := read_past _ _ _ _ _ _ (by decide)

section Meaning

variable (r : EcRingOps) (ρ : OpEnv)

theorem onerNeq0_iff :
    importedPropWithOps ProcEnv.empty ρ r.onerNeq0Form
      ↔ r.cstV ρ r.one ≠ r.cstV ρ r.zero := by
  simp [importedPropWithOps, transForm, EcRingOps.onerNeq0Form, EcRingOps.cstV]

theorem addr0_iff :
    importedPropWithOps ProcEnv.empty ρ r.addr0Form
      ↔ ∀ x : r.ty.interp, r.binV ρ r.add x (r.cstV ρ r.zero) = x := by
  simp [importedPropWithOps, EcRingOps.addr0Form, EcRingOps.varX, EcRingOps.binV,
    EcRingOps.cstV, FormEnv.bindVar]

theorem addrA_iff :
    importedPropWithOps ProcEnv.empty ρ r.addrAForm
      ↔ ∀ x y z : r.ty.interp,
          r.binV ρ r.add x (r.binV ρ r.add y z)
            = r.binV ρ r.add (r.binV ρ r.add x y) z := by
  simp [importedPropWithOps, EcRingOps.addrAForm, EcRingOps.varX, EcRingOps.varY,
    EcRingOps.varZ, EcRingOps.binV, FormEnv.bindVar]

theorem addrC_iff :
    importedPropWithOps ProcEnv.empty ρ r.addrCForm
      ↔ ∀ x y : r.ty.interp, r.binV ρ r.add x y = r.binV ρ r.add y x := by
  simp [importedPropWithOps, EcRingOps.addrCForm, EcRingOps.varX, EcRingOps.varY,
    EcRingOps.binV, FormEnv.bindVar]

theorem addrN_iff (opp : String) :
    importedPropWithOps ProcEnv.empty ρ (r.addrNForm opp)
      ↔ ∀ x : r.ty.interp, r.binV ρ r.add x (r.unV ρ opp x) = r.cstV ρ r.zero := by
  simp [importedPropWithOps, EcRingOps.addrNForm, EcRingOps.varX, EcRingOps.binV,
    EcRingOps.unV, EcRingOps.cstV, FormEnv.bindVar]

theorem addrK_iff :
    importedPropWithOps ProcEnv.empty ρ r.addrKForm
      ↔ ∀ x : r.ty.interp, r.binV ρ r.add x x = r.cstV ρ r.zero := by
  simp [importedPropWithOps, EcRingOps.addrKForm, EcRingOps.varX, EcRingOps.binV,
    EcRingOps.cstV, FormEnv.bindVar]

theorem opprId_iff (opp : String) :
    importedPropWithOps ProcEnv.empty ρ (r.opprIdForm opp)
      ↔ ∀ x : r.ty.interp, r.unV ρ opp x = x := by
  simp [importedPropWithOps, EcRingOps.opprIdForm, EcRingOps.varX, EcRingOps.unV,
    FormEnv.bindVar]

theorem mulr1_iff :
    importedPropWithOps ProcEnv.empty ρ r.mulr1Form
      ↔ ∀ x : r.ty.interp, r.binV ρ r.mul x (r.cstV ρ r.one) = x := by
  simp [importedPropWithOps, EcRingOps.mulr1Form, EcRingOps.varX, EcRingOps.binV,
    EcRingOps.cstV, FormEnv.bindVar]

theorem mulrA_iff :
    importedPropWithOps ProcEnv.empty ρ r.mulrAForm
      ↔ ∀ x y z : r.ty.interp,
          r.binV ρ r.mul x (r.binV ρ r.mul y z)
            = r.binV ρ r.mul (r.binV ρ r.mul x y) z := by
  simp [importedPropWithOps, EcRingOps.mulrAForm, EcRingOps.varX, EcRingOps.varY,
    EcRingOps.varZ, EcRingOps.binV, FormEnv.bindVar]

theorem mulrC_iff :
    importedPropWithOps ProcEnv.empty ρ r.mulrCForm
      ↔ ∀ x y : r.ty.interp, r.binV ρ r.mul x y = r.binV ρ r.mul y x := by
  simp [importedPropWithOps, EcRingOps.mulrCForm, EcRingOps.varX, EcRingOps.varY,
    EcRingOps.binV, FormEnv.bindVar]

theorem mulrDl_iff :
    importedPropWithOps ProcEnv.empty ρ r.mulrDlForm
      ↔ ∀ x y z : r.ty.interp,
          r.binV ρ r.mul (r.binV ρ r.add x y) z
            = r.binV ρ r.add (r.binV ρ r.mul x z) (r.binV ρ r.mul y z) := by
  simp [importedPropWithOps, EcRingOps.mulrDlForm, EcRingOps.varX, EcRingOps.varY,
    EcRingOps.varZ, EcRingOps.binV, FormEnv.bindVar]

theorem mulrK_iff :
    importedPropWithOps ProcEnv.empty ρ r.mulrKForm
      ↔ ∀ x : r.ty.interp, r.binV ρ r.mul x x = x := by
  simp [importedPropWithOps, EcRingOps.mulrKForm, EcRingOps.varX, EcRingOps.binV,
    FormEnv.bindVar]

theorem expr0_iff (e : String) :
    importedPropWithOps ProcEnv.empty ρ (r.expr0Form e)
      ↔ ∀ x : r.ty.interp, r.expV ρ e x 0 = r.cstV ρ r.one := by
  simp [importedPropWithOps, EcRingOps.expr0Form, EcRingOps.varX, EcRingOps.expV,
    EcRingOps.cstV, FormEnv.bindVar]

theorem exprS_iff (e : String) :
    importedPropWithOps ProcEnv.empty ρ (r.exprSForm e)
      ↔ ∀ (x : r.ty.interp) (n : Int), 0 ≤ n →
          r.expV ρ e x (n + 1) = r.binV ρ r.mul x (r.expV ρ e x n) := by
  simp [importedPropWithOps, EcRingOps.exprSForm, ringNNonneg, ringVarN,
    ringVarNSucc, EcRingOps.varX, EcRingOps.expV, EcRingOps.binV, FormEnv.bindVar]

theorem ofint0_iff (emb : String) :
    importedPropWithOps ProcEnv.empty ρ (r.ofint0Form emb)
      ↔ r.embV ρ emb 0 = r.cstV ρ r.zero := by
  simp [importedPropWithOps, EcRingOps.ofint0Form, EcRingOps.embV, EcRingOps.cstV]

theorem ofint1_iff (emb : String) :
    importedPropWithOps ProcEnv.empty ρ (r.ofint1Form emb)
      ↔ r.embV ρ emb 1 = r.cstV ρ r.one := by
  simp [importedPropWithOps, EcRingOps.ofint1Form, EcRingOps.embV, EcRingOps.cstV]

theorem ofintS_iff (emb : String) :
    importedPropWithOps ProcEnv.empty ρ (r.ofintSForm emb)
      ↔ ∀ n : Int, 0 ≤ n →
          r.embV ρ emb (n + 1) = r.binV ρ r.add (r.cstV ρ r.one) (r.embV ρ emb n) := by
  simp [importedPropWithOps, EcRingOps.ofintSForm, ringNNonneg, ringVarN,
    ringVarNSucc, EcRingOps.embV, EcRingOps.binV, EcRingOps.cstV, FormEnv.bindVar]

theorem ofintN_iff (emb opp : String) :
    importedPropWithOps ProcEnv.empty ρ (r.ofintNForm emb opp)
      ↔ ∀ n : Int, r.embV ρ emb (-n) = r.unV ρ opp (r.embV ρ emb n) := by
  simp [importedPropWithOps, EcRingOps.ofintNForm, ringVarN, ringVarNeg,
    EcRingOps.embV, EcRingOps.unV, FormEnv.bindVar]

theorem subrE_iff (sub opp : String) :
    importedPropWithOps ProcEnv.empty ρ (r.subrEForm sub opp)
      ↔ ∀ x y : r.ty.interp,
          r.binV ρ sub x y = r.binV ρ r.add x (r.unV ρ opp y) := by
  simp [importedPropWithOps, EcRingOps.subrEForm, EcRingOps.varX, EcRingOps.varY,
    EcRingOps.binV, EcRingOps.unV, FormEnv.bindVar]

theorem mulrV_iff (inv : String) :
    importedPropWithOps ProcEnv.empty ρ (r.mulrVForm inv)
      ↔ ∀ x : r.ty.interp, x ≠ r.cstV ρ r.zero →
          r.binV ρ r.mul x (r.unV ρ inv x) = r.cstV ρ r.one := by
  simp [importedPropWithOps, transForm, EcRingOps.mulrVForm, EcRingOps.varX,
    EcRingOps.binV, EcRingOps.unV, EcRingOps.cstV, FormEnv.bindVar]

/-- The third binder of `exprN` is the negation of the second, so the law is the
negation form EasyCrypt states. -/
theorem exprN_iff (e inv : String) :
    importedPropWithOps ProcEnv.empty ρ (r.exprNForm e inv)
      ↔ ∀ (x : r.ty.interp) (n : Int), 0 ≤ n →
          r.expV ρ e x (-n) = r.unV ρ inv (r.expV ρ e x n) := by
  simp [importedPropWithOps, EcRingOps.exprNForm, ringNNonneg, ringVarN,
    ringVarNeg, EcRingOps.varX, EcRingOps.expV, EcRingOps.unV, FormEnv.bindVar]

theorem divrE_iff (div inv : String) :
    importedPropWithOps ProcEnv.empty ρ (r.divrEForm div inv)
      ↔ ∀ x y : r.ty.interp,
          r.binV ρ div x y = r.binV ρ r.mul x (r.unV ρ inv y) := by
  simp [importedPropWithOps, EcRingOps.divrEForm, EcRingOps.varX, EcRingOps.varY,
    EcRingOps.binV, EcRingOps.unV, FormEnv.bindVar]

theorem CnEq0_iff (emb : String) (c : Int) :
    importedPropWithOps ProcEnv.empty ρ (r.CnEq0Form emb c)
      ↔ r.embV ρ emb c = r.cstV ρ r.zero := by
  simp [importedPropWithOps, EcRingOps.CnEq0Form, EcRingOps.embV, EcRingOps.cstV]

theorem CpIdp_iff (e : String) (p : Int) :
    importedPropWithOps ProcEnv.empty ρ (r.CpIdpForm e p)
      ↔ ∀ x : r.ty.interp, r.expV ρ e x p = x := by
  simp [importedPropWithOps, EcRingOps.CpIdpForm, EcRingOps.varX, EcRingOps.expV,
    FormEnv.bindVar]

end Meaning

/-! ## A general instance bundles nothing -/

/-- A general instance obliges no law: it names a class and carries no
operators. -/
theorem general_obligations_isError (p : String) :
    ∃ e, (EcInstanceBody.general p).obligations = .error e := ⟨_, rfl⟩

/-- An instance the decoder gives no image has no satisfying realization, so a
rejection cannot be read as an empty bundle every realization meets. -/
theorem not_satisfiedBy_of_error (i : EcInstance) (ρ : OpEnv) (e : String)
    (h : i.obligations = .error e) : ¬ i.satisfiedBy ρ := by
  simp [EcInstance.satisfiedBy, h]

/-! ## The corpus payloads

The literals below are the `Th_instance` items of `algebra/StdRing.ec` and
`algebra/CyclicGroup.ec` as the exporter writes them at schema version
`schemaVersion`, built with the node combinators the rest of the ingestion's
checks use. -/

/-- A nullary type-constructor node at the path `p`. -/
private def jInstTyC (p : String) : Json :=
  Json.mkObj [("kind", Json.str "Tconstr"), ("path", Json.str p),
              ("args", Json.arr #[])]

/-- A `Th_instance` item for the type at `ty`, holding the instance node. -/
private def jInstItem (ty : String) (inst : Json) : Json :=
  Json.mkObj [("kind", Json.str "Th_instance"), ("tparams", Json.arr #[]),
              ("ty", jInstTyC ty), ("locality", Json.str "global"),
              ("instance", inst)]

/-- The `Th_instance` item of `StdRing.ec`'s `instance ring with int`. -/
def jStdRingIntInstance : Json :=
  jInstItem "Top.Pervasive.int"
    (Json.mkObj
      [("kind", Json.str "Ring"),
       ("ring", Json.mkObj
         [("name", Json.null), ("ty", jInstTyC "Top.Pervasive.int"),
          ("zero", Json.str "Top.CoreInt.zero"), ("one", Json.str "Top.CoreInt.one"),
          ("add", Json.str "Top.CoreInt.add"), ("opp", Json.str "Top.CoreInt.opp"),
          ("mul", Json.str "Top.CoreInt.mul"), ("exp", Json.str "Top.Ring.IntID.exp"),
          ("sub", Json.null),
          ("embed", Json.mkObj [("kind", Json.str "Direct")]),
          ("rkind", Json.mkObj [("kind", Json.str "Integer")])])])

/-- The `Th_instance` item of `StdRing.ec`'s `instance bring with bool`. -/
def jStdRingBoolInstance : Json :=
  jInstItem "Top.Pervasive.bool"
    (Json.mkObj
      [("kind", Json.str "Ring"),
       ("ring", Json.mkObj
         [("name", Json.null), ("ty", jInstTyC "Top.Pervasive.bool"),
          ("zero", Json.str "Top.Pervasive.false"),
          ("one", Json.str "Top.Pervasive.true"),
          ("add", Json.str "Top.Bool.^^"), ("opp", Json.str "Top.bid"),
          ("mul", Json.str "Top.Pervasive./\\"), ("exp", Json.null),
          ("sub", Json.null),
          ("embed", Json.mkObj [("kind", Json.str "Default")]),
          ("rkind", Json.mkObj [("kind", Json.str "Boolean")])])])

/-- One of the `General` items `StdRing.ec`'s ring declaration binds beside its
`Ring` item. -/
def jStdRingIntZmodule : Json :=
  jInstItem "Top.Pervasive.int"
    (Json.mkObj [("kind", Json.str "General"),
                 ("path", Json.str "Top.Ring.ZModule.zmodule")])

/-- The `Th_instance` item of `CyclicGroup.ec`'s field declaration, whose carrier
is a declared type rather than a prelude one. -/
def jCyclicFieldInstance : Json :=
  jInstItem "Top.CyclicGroup.PowZMod.ZModE.exp"
    (Json.mkObj
      [("kind", Json.str "Field"),
       ("ring", Json.mkObj
         [("name", Json.null), ("ty", jInstTyC "Top.CyclicGroup.PowZMod.ZModE.exp"),
          ("zero", Json.str "Top.CyclicGroup.PowZMod.ZModE.zero"),
          ("one", Json.str "Top.CyclicGroup.PowZMod.ZModE.one"),
          ("add", Json.str "Top.CyclicGroup.PowZMod.ZModE.+"),
          ("opp", Json.str "Top.CyclicGroup.PowZMod.ZModE.[-]"),
          ("mul", Json.str "Top.CyclicGroup.PowZMod.ZModE.*"),
          ("exp", Json.str "Top.CyclicGroup.PowZMod.ZModE.ZModpRing.exp"),
          ("sub", Json.null),
          ("embed", Json.mkObj [("kind", Json.str "Default")]),
          ("rkind", Json.mkObj [("kind", Json.str "Integer")])]),
       ("inv", Json.str "Top.CyclicGroup.PowZMod.ZModE.inv"),
       ("div", Json.null)])

/-! ## The decoded corpus instances -/

/-- The operators of `StdRing.ec`'s `instance ring with int`. It is reducible:
a realization of these operators is a function at `ty.interp`, and the carrier
has to reduce for the arithmetic instances at it to be found. -/
@[reducible] def stdRingIntOps : EcRingOps where
  name := none
  ty := .int
  zero := "Top.CoreInt.zero"
  one := "Top.CoreInt.one"
  add := "Top.CoreInt.add"
  opp := some "Top.CoreInt.opp"
  mul := "Top.CoreInt.mul"
  exp := some "Top.Ring.IntID.exp"
  sub := none
  embed := .direct
  rkind := .integer

/-- `StdRing.ec`'s `instance ring with int`. -/
def stdRingIntInstance : EcInstance where
  tparams := []
  ty := .int
  locality := .global
  body := .ring stdRingIntOps

/-- The operators of `StdRing.ec`'s `instance bring with bool`, reducible for the
reason `stdRingIntOps` is. -/
@[reducible] def stdRingBoolOps : EcRingOps where
  name := none
  ty := .bool
  zero := "Top.Pervasive.false"
  one := "Top.Pervasive.true"
  add := "Top.Bool.^^"
  opp := some "Top.bid"
  mul := "Top.Pervasive./\\"
  exp := none
  sub := none
  embed := .dflt
  rkind := .boolean

/-- `StdRing.ec`'s `instance bring with bool`. -/
def stdRingBoolInstance : EcInstance where
  tparams := []
  ty := .bool
  locality := .global
  body := .ring stdRingBoolOps

/-- The tables `CyclicGroup.ec`'s field declaration decodes against: its carrier
is a declared type, which the type walk registers at an opaque code. -/
def cyclicFieldTables : DecodeTables :=
  ecPrelude.withOpaqueType "Top.CyclicGroup.PowZMod.ZModE.exp"

/-! ## The decode, end to end -/

-- The `Ring` item decodes to the operator set the declaration names, with the
-- subtraction absent and the embedding direct.
#guard (match decodeThInstance ecPrelude jStdRingIntInstance with
        | .ok i => i == stdRingIntInstance
        | _ => false)

-- The `bring` item decodes at the boolean kind, with no exponentiation.
#guard (match decodeThInstance ecPrelude jStdRingBoolInstance with
        | .ok i => i == stdRingBoolInstance
        | _ => false)

-- The field item decodes at the carrier the type walk registers, with the
-- inversion named and the division absent.
#guard (match decodeThInstance cyclicFieldTables jCyclicFieldInstance with
        | .ok i =>
            i.ty == EcTy.opaque "Top.CyclicGroup.PowZMod.ZModE.exp"
              && (match i.body with
                  | .field r inv div =>
                      r.exp == some "Top.CyclicGroup.PowZMod.ZModE.ZModpRing.exp"
                        && inv == "Top.CyclicGroup.PowZMod.ZModE.inv"
                        && div == none
                  | _ => false)
        | _ => false)

-- A carrier the ingestion has not registered has no code, so the instance does
-- not decode against the prelude alone.
#guard (match decodeThInstance ecPrelude jCyclicFieldInstance with
        | .error _ => true
        | _ => false)

-- The general item decodes to the class path it names.
#guard (match decodeThInstance ecPrelude jStdRingIntZmodule with
        | .ok i => i.body == .general "Top.Ring.ZModule.zmodule"
        | _ => false)

/-! ## The obligations of the decoded instances -/

/-- `instance ring with int` names an opposite and an exponentiation and no
subtraction, and its embedding is direct, so it is obliged to the nine core
axioms and the two exponentiation axioms. -/
theorem stdRingInt_obligation_names :
    stdRingIntInstance.obligations.map (List.map Prod.fst)
      = .ok ["oner_neq0", "addr0", "addrA", "addrC", "addrN", "mulr1", "mulrA",
             "mulrC", "mulrDl", "expr0", "exprS"] := rfl

/-- `instance bring with bool` is at the boolean kind, so `addrN` is replaced by
`addrK` and `mulrK`, and naming an opposite obliges `oppr_id`. Naming no
exponentiation is what keeps `expr0` and `exprS` off the list. -/
theorem stdRingBool_obligation_names :
    stdRingBoolInstance.obligations.map (List.map Prod.fst)
      = .ok ["oner_neq0", "addr0", "addrA", "addrC", "addrK", "mulrK", "mulr1",
             "mulrA", "mulrC", "mulrDl", "oppr_id"] := rfl

/-- Each operator the int ring names, at the signature the declaration gives
it. -/
theorem stdRingInt_opSigs :
    stdRingIntInstance.opSigs
      = [("Top.CoreInt.zero", ⟨.unit, .int⟩), ("Top.CoreInt.one", ⟨.unit, .int⟩),
         ("Top.CoreInt.add", ⟨.prod .int .int, .int⟩),
         ("Top.CoreInt.mul", ⟨.prod .int .int, .int⟩),
         ("Top.CoreInt.opp", ⟨.int, .int⟩),
         ("Top.Ring.IntID.exp", ⟨.prod .int .int, .int⟩)] := rfl

/-- A goal stated under the int ring's obligations reads no operator it does not
bind: `EcForm.assembleParams` puts one binder around it per operator the goal and
the premises read. -/
theorem stdRingInt_underLaws_opsOf :
    (stdRingIntInstance.underLaws .tru).map EcForm.opsOf = .ok [] := rfl

/-- The same for the boolean ring. -/
theorem stdRingBool_underLaws_opsOf :
    (stdRingBoolInstance.underLaws .tru).map EcForm.opsOf = .ok [] := rfl

end CatCrypt.Crypto.EasyCryptImport
