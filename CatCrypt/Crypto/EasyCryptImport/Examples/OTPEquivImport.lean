/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.FormJson
import CatCrypt.Crypto.EasyCryptImport.FormToProp
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPImport
import CatCryptCore.Relational.Rules
import CatCryptCore.Relational.Frame

/-!
# Worked example: an EasyCrypt lemma from source text to a closed Lean goal

This module takes one export — `otpequiv.expected.json`, the output of
`ec2json` on an EasyCrypt file declaring the two one-time-pad games and three
statements about them — and carries both the games and a statement through the
whole importer: JSON, AST, translation, proof.

The source the export comes from is

```
module OTP0 = { proc main() : bool = { var k, c : bool; k <$ {0,1};
                                       c <- k ^ false; return c; } }.
module OTP1 = { proc main() : bool = { var k, c : bool; k <$ {0,1};
                                       c <- k ^ true;  return c; } }.

lemma otp_equiv : equiv [OTP0.main ~ OTP1.main : true ==> ={res}].
```

## What is machine-checked, and where the `#guard`s come in

`decodeGame` and `decodeForm` recurse on the `jsonSize` measure, and well-founded
recursion is not definitionally reducible, so a `Prop` stated as "the translation
of whatever the decoder returns" would not reduce to anything a proof could work
with. The AST values below are therefore written out, and each is pinned to the
decoder's output by a `#guard` whose pattern is fully concrete — every field a
literal — so the match holds exactly when the decoder returns that value. The
`#guard`s run when this module is built, and a change in the exporter, the
fixture or the decoder that moved any of these values would fail the build.

## The three statements of the export

`otp_equiv` is the one carried through to a proof here. The other two are
probability statements over the same two games:

```
lemma otp_pr_eq : forall &m, Pr[OTP0.main() @ &m : res] = Pr[OTP1.main() @ &m : res].
lemma otp_pr_diff : forall &m,
  `|Pr[OTP0.main() @ &m : res] - Pr[OTP1.main() @ &m : res]| = 0%r.
```

Their decoded ASTs are pinned below too, which is what exercises `EcProb.pr`,
`EcProb.absDiff` and `EcProb.const` against real exporter output.

## The precondition is `true`, not memory equality

`Form.lean`'s `EcForm.memEq` — the two memories are equal — has no EasyCrypt
surface source. EasyCrypt has no whole-memory equality: `={glob M}` is expanded
by the typechecker into one equality per `var` of `M`, and into `tt = tt` when
`M` declares none, so the strongest precondition an EasyCrypt `equiv` over these
two games can carry is `true`. The imported goal is therefore *not* the statement
of `OTPImport.otpImport_coupling`, and the two are not comparable: the imported
judgement has the weaker precondition (`True` against `eqPre`) and the weaker
postcondition (results equal, against results and memories equal).

`otpImport_coupling_gen` below is the coupling both statements are instances of:
the coupling at a parametric precondition. It is the `xor`-by-`(m₀ ^ m₁)`
coupling at `truePre` framed by `Relational.r_frame_of_preservesNothing`, which
carries an arbitrary precondition across two computations that modify no heap
location. `otpImport_coupling_of_gen` recovers `OTPImport.otpImport_coupling`'s
statement from it definitionally, and `otpEquivGoal_holds` gets the imported goal
from it by weakening the postcondition.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport.OTPEquivImport

open Lean (Json)
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Prob.XorBij
open CatCrypt.Crypto.EasyCryptBridge
open CatCrypt.Crypto.EasyCryptImport.OTPImport
open scoped ENNReal

/-! ## The export -/

/-- The exporter's output for the one-time-pad equivalence theory, as text. -/
private def otpEquivExportText : String := include_str "../otpequiv.expected.json"

/-- The exporter's output for the one-time-pad equivalence theory. -/
private def otpEquivExport : Json :=
  match Json.parse otpEquivExportText with
  | .ok j => j
  | .error _ => Json.null

-- The fixture parses, and it is an export of the source file it claims.
#guard (match decodeEnvelope otpEquivExport with
        | .ok e => e.source == "tests/otpequiv.ec" && e.root == "Top"
        | _ => false)

/-! ## The games

Both modules decode to the shape `OTPImport.otpGame` has, differing from it only
in the source name each carries. -/

/-- The one-time-pad game at message `m` under the source name `nm`: the AST both
modules of the export decode to. -/
def otpGameNamed (nm : String) (m : Bool) : EcGame where
  name := nm
  locals := ["k", "c"]
  body :=
    [ EcStmt.sample .bool "k",
      EcStmt.assign .bool "c" (EcExpr.bxor (EcExpr.var .bool "k") (EcExpr.lit m)) ]
  ret := EcExpr.var .bool "c"

/-- The source name is provenance: a named game lowers to the computation
`OTPImport.otpGame` lowers to. -/
theorem lowerClosedGame_otpGameNamed (nm : String) (m : Bool) :
    lowerClosedGame OpEnv.empty (otpGameNamed nm m) = lowerClosedGame OpEnv.empty (otpGame m) := rfl

-- `OTP0` decodes to the game at message `false`.
#guard (match importGame ecPrelude "OTP0" otpEquivExport with
        | .ok { name := "OTP0", locals := ["k", "c"], procs := [],
                body := [.sample .bool "k",
                         .assign .bool "c" (.bxor (.var .bool "k") (.lit false))],
                ret := .var .bool "c" } => true
        | _ => false)

-- `OTP1` decodes to the game at message `true`.
#guard (match importGame ecPrelude "OTP1" otpEquivExport with
        | .ok { name := "OTP1", locals := ["k", "c"], procs := [],
                body := [.sample .bool "k",
                         .assign .bool "c" (.bxor (.var .bool "k") (.lit true))],
                ret := .var .bool "c" } => true
        | _ => false)

/-! ## The statement tables

The signature a judgement carries comes from the export's own modules, not from
this file: `procSigsOfStructure` reads it off each decoded module body. -/

/-- The signature of every procedure the export declares, keyed by the path a
judgement names it by. -/
def otpProcSigs : Except String (List (String × EcSig)) := do
  let e ← decodeEnvelope otpEquivExport
  let i₀ ← findItem e "OTP0"
  let i₁ ← findItem e "OTP1"
  let S₀ ← decodeStructure ecPrelude 0 i₀
  let S₁ ← decodeStructure ecPrelude 100 i₁
  .ok (procSigsOfStructure S₀ ++ procSigsOfStructure S₁)

-- The two `main` procedures are argument-free and return a bit.
#guard (match otpProcSigs with
        | .ok [("Top.OTP0./main", ⟨.unit, .bool⟩), ("Top.OTP1./main", ⟨.unit, .bool⟩)] =>
          true
        | _ => false)

/-- The tables the three statements of the export decode against. -/
def otpFormTables : Except String FormTables := do
  let sigs ← otpProcSigs
  .ok (formTables ecPrelude sigs)

/-- Decode the statement of the lemma `name` from the export. -/
def importedStatement (name : String) : Except String EcForm := do
  let F ← otpFormTables
  importAxiom F name otpEquivExport

/-! ## The imported relational judgement -/

/-- The signature of an argument-free game, `proc main() : bool`. -/
def mainSig : EcSig := ⟨.unit, .bool⟩

/-- The statement of `otp_equiv`, as the decoder produces it. -/
def otpEquivForm : EcForm :=
  .equiv "Top.OTP0./main" mainSig (.lit (t := .unit) ())
         "Top.OTP1./main" mainSig (.lit (t := .unit) ())
    .tru (.eqT (.res .bool .left) (.res .bool .right))

-- The decoder produces exactly that form.
#guard (match importedStatement "otp_equiv" with
        | .ok (.equiv "Top.OTP0./main" ⟨.unit, .bool⟩ (.lit ())
                      "Top.OTP1./main" ⟨.unit, .bool⟩ (.lit ())
                 .tru (.eqT (.res .bool .left) (.res .bool .right))) => true
        | _ => false)

/-! ## The imported probability statements

These are decoded and pinned, not proved: they exercise `EcProb` against real
exporter output. `Pr[q() @ &m : res]` is `EcProb.prTrueOf`. -/

/-- The statement of `otp_pr_eq`, as the decoder produces it. -/
def otpPrEqForm : EcForm :=
  .allMem "&m"
    (.probCmp .eq (EcProb.prTrueOf "Top.OTP0./main" (.lit (t := .unit) ()) (.named "&m"))
      (EcProb.prTrueOf "Top.OTP1./main" (.lit (t := .unit) ()) (.named "&m")))

-- The decoder produces exactly that form: a memory quantifier over an equality
-- of two `Pr[… : res]` nodes, each at the quantified memory.
#guard (match importedStatement "otp_pr_eq" with
        | .ok (.allMem "&m"
                (.probCmp .eq
                  (.pr "Top.OTP0./main" ⟨.unit, .bool⟩ (.lit ()) (.named "&m")
                     (.holds (.res .bool .cur)))
                  (.pr "Top.OTP1./main" ⟨.unit, .bool⟩ (.lit ()) (.named "&m")
                     (.holds (.res .bool .cur))))) => true
        | _ => false)

/-- The statement of `otp_pr_diff`, as the decoder produces it. -/
def otpPrDiffForm : EcForm :=
  .allMem "&m"
    (EcForm.prDiffCmp .eq "Top.OTP0./main" (.lit (t := .unit) ())
      "Top.OTP1./main" (.lit (t := .unit) ()) (.named "&m") (EcProb.const (EcRealLit.mk 0 1)))

-- The decoder produces that form: EasyCrypt writes the difference as
-- `add a (opp b)` under an absolute value, and that is the only shape with an
-- `EcProb.absDiff` image. The guard pins the value of the bound as well as the
-- shape of the statement, since `EcRealLit` carries the numeral the decoder read.
#guard (match importedStatement "otp_pr_diff" with
        | .ok (.allMem "&m"
                (.probCmp .eq
                  (.absDiff
                    (.pr "Top.OTP0./main" ⟨.unit, .bool⟩ (.lit ()) (.named "&m")
                       (.holds (.res .bool .cur)))
                    (.pr "Top.OTP1./main" ⟨.unit, .bool⟩ (.lit ()) (.named "&m")
                       (.holds (.res .bool .cur))))
                  (EcProb.const (EcRealLit.mk 0 1)))) => true
        | _ => false)

/-! ## The resolution environment

The two games the statement names are the two the export declares, under the
paths the export names them by. -/

/-- The environment the imported statements resolve against. -/
noncomputable def otpEnv : ProcEnv :=
  (ProcEnv.empty.bindProc "Top.OTP0./main" (s := mainSig)
      (fun _ => lowerClosedGame OpEnv.empty (otpGameNamed "OTP0" false))).bindProc
    "Top.OTP1./main" (s := mainSig)
      (fun _ => lowerClosedGame OpEnv.empty (otpGameNamed "OTP1" true))

/-! ## The goal, and its proof -/

/-- The imported statement of `otp_equiv`, as a goal. -/
noncomputable def otpEquivGoal : Prop := importedProp otpEnv otpEquivForm

/-- The translated goal is the pRHL judgement between the two lowered games, with
the trivial precondition the source writes and equality of the two results. -/
theorem otpEquivGoal_eq :
    otpEquivGoal
      = pRHL truePre (lowerClosedGame OpEnv.empty (otpGame false)) (lowerClosedGame OpEnv.empty (otpGame true))
          (fun r₁ (_ : Heap) r₂ (_ : Heap) => r₁ = r₂) :=
  rfl

/-- The one-time-pad coupling at the trivial precondition: the uniform key masks
the message, so `xor`-by-`(m₀ ^ m₁)` couples the two runs and the two results
agree. -/
theorem otpImport_coupling_true (m₀ m₁ : Bool) :
    pRHL truePre (lowerClosedGame OpEnv.empty (otpGame m₀)) (lowerClosedGame OpEnv.empty (otpGame m₁))
      (fun r₁ (_ : Heap) r₂ (_ : Heap) => r₁ = r₂) := by
  rw [lowerGame_otpGame, lowerGame_otpGame]
  refine rHoare_bij_step (boolXorBij (xor m₀ m₁)) fun a => rHoare_ret fun _ _ _ => ?_
  cases a <;> cases m₀ <;> cases m₁ <;> rfl

/-- The lowered game modifies no heap location: it samples a key and returns a
value, and neither step writes. -/
theorem preservesOutside_lowerClosedGame_otpGame (m : Bool) :
    PreservesOutside (lowerClosedGame OpEnv.empty (otpGame m)) ∅ := by
  rw [lowerGame_otpGame]
  simpa using
    preservesOutside_bind (preservesOutside_sample Bool)
      (fun k => preservesOutside_pure (xor k m))

/-- The one-time-pad coupling at an arbitrary precondition, by framing. The two
games modify nothing, so `Relational.r_frame_of_preservesNothing` carries `Φ`
from the initial pair of memories to the final pair and conjoins it to the
postcondition of the coupling at `truePre`. -/
theorem otpImport_coupling_gen (Φ : RPre) (m₀ m₁ : Bool) :
    pRHL Φ (lowerClosedGame OpEnv.empty (otpGame m₀)) (lowerClosedGame OpEnv.empty (otpGame m₁))
      (fun r₁ h₁ r₂ h₂ => r₁ = r₂ ∧ Φ h₁ h₂) :=
  r_frame_of_preservesNothing
    (preservesOutside_lowerClosedGame_otpGame m₀)
    (preservesOutside_lowerClosedGame_otpGame m₁)
    (otpImport_coupling_true m₀ m₁)

/-- At `eqPre` the general coupling is `OTPImport.otpImport_coupling`'s
statement, definitionally: `eqPost` is equality of results conjoined with
`eqPre` of the two final memories. -/
theorem otpImport_coupling_of_gen (m₀ m₁ : Bool) :
    pRHL eqPre (lowerClosedGame OpEnv.empty (otpGame m₀)) (lowerClosedGame OpEnv.empty (otpGame m₁)) eqPost :=
  otpImport_coupling_gen eqPre m₀ m₁

/-- The imported goal, closed: the translation of the exported `equiv` lemma
follows from the general coupling by weakening the postcondition. -/
theorem otpEquivGoal_holds : otpEquivGoal :=
  otpEquivGoal_eq ▸ rHoare_mono_post (otpImport_coupling_gen truePre false true)
    (fun _ _ _ _ h => h.1)

end CatCrypt.Crypto.EasyCryptImport.OTPEquivImport
