/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Emit
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPGenerated
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPArgGenerated
import CatCrypt.Crypto.EasyCryptImport.Examples.NegGenerated
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPImport

/-!
# EasyCrypt import: the emitter's round trip

This module closes the chain from the exporter's JSON to an elaborated AST for the
one-time-pad export `otp.expected.json` and for the functor `Neg` of
`functor.expected.json`.

**The committed file is the emitter's output.** For each of the three generated
files, a `#guard` decodes the export and compares `emitFromJson`'s text with the
committed file's text, read by `include_str`. A hand edit to a generated file, or
emitter drift, fails the check.

**The elaborated game is the hand-written game.** `otp0Game_eq_otpGame` is a `rfl`
proof that the literal `Examples/OTPGenerated.lean` elaborates to is
`OTPImport.otpGame false`, the hand-written `EcGame` of the worked example, under
the source name `OTP0` the exported module carries — `EcGame.name` is provenance
and is the one field the two differ in. The golden `#guard` of `Json.lean` matches
`importGame ecPrelude "OTP0"` against that same shape at that same name, so the
two links pin the decoder's output and the generated file's elaboration to one
literal.

**The generated literal carries the proofs.** `generated_otp0_advantage_zero`
transports the worked example's zero-advantage result to the generated game along
that equality.

**Every constructor round-trips.** The one-time-pad export reaches nine AST
constructors. Each of the others has a declaration whose body is written exactly as
the emitter prints it, together with a `#guard` that the emitter prints that text;
`EcStmt.forN` is among them, and has no decoder image, so its check covers the
emitter alone. `EcStmt.sampleD` has one check per `EcDistr` constructor, and one
more at a stamped binder, which is the branch of `emitVarId` a decoded
distribution operator reaches.

For the module `OTPArg` there is no hand-written literal to compare with, so the
checks below match `Generated.otpArgModule` against the shapes the golden
`#guard`s of `Json.lean` match `importModule ecPrelude "OTPArg"` against: the
module name, the declared names, the signature of `enc`, the emptiness of the
globals, and the body of each of the two procedures. Those are the components the
patterns name; nothing pins a component no pattern mentions.

The functor `Generated.negFunctor` is matched the same way, against the shape
`Examples/FunctorImport.lean` matches `importFunctor ecPrelude "Neg"` against:
the functor's name, the parameter's name and interface, and the body's declared
name, signature and statement.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)
open CatCrypt.Core CatCrypt.Crypto

/-! ## The committed files are the emitter's output -/

/-- The exporter's output for the one-time-pad theory. -/
private def otpExport : Json :=
  match Json.parse (include_str "otp.expected.json") with
  | .ok j => j
  | .error _ => Json.null

/-- The committed generated module for the game `OTP0`. -/
private def otpGeneratedText : String := include_str "Examples/OTPGenerated.lean"

/-- The committed generated module for the module `OTPArg`. -/
private def otpArgGeneratedText : String :=
  include_str "Examples/OTPArgGenerated.lean"

-- `Examples/OTPGenerated.lean` is what the emitter prints for `OTP0`.
#guard (match emitFromJson ecPrelude "game" "OTP0" "otp0Game" otpExport with
        | .ok s => s == otpGeneratedText
        | .error _ => false)

-- `Examples/OTPArgGenerated.lean` is what the emitter prints for `OTPArg`.
#guard (match emitFromJson ecPrelude "module" "OTPArg" "otpArgModule" otpExport with
        | .ok s => s == otpArgGeneratedText
        | .error _ => false)

/-- The exporter's output for the two-functor theory. -/
private def functorExport : Json :=
  match Json.parse (include_str "functor.expected.json") with
  | .ok j => j
  | .error _ => Json.null

/-- The committed generated module for the functor `Neg`. -/
private def negGeneratedText : String := include_str "Examples/NegGenerated.lean"

-- `Examples/NegGenerated.lean` is what the emitter prints for `Neg`.
#guard (match emitFromJson ecPrelude "functor" "Neg" "negFunctor" functorExport with
        | .ok s => s == negGeneratedText
        | .error _ => false)

-- A module of no parameter has no functor image, and a functor has no module
-- image: each decoder rejects the other's item rather than producing a value.
#guard (match emitFromJson ecPrelude "functor" "OTPArg" "d" otpExport with
        | .error _ => true
        | .ok _ => false)

#guard (match emitFromJson ecPrelude "module" "Neg" "d" functorExport with
        | .error _ => true
        | .ok _ => false)

/-! ## The elaborated game is the hand-written game -/

/-- The `EcGame` the generated module elaborates to is the hand-written `otpGame`
of the worked example, at the message bit `false`, carrying the source module's
name. `EcGame.name` is the source name for provenance: the exported module is
`OTP0` and the worked example calls the same game `OTP`, so the equality is at the
renamed game, and every other field is equal on the nose. -/
theorem otp0Game_eq_otpGame :
    Generated.otp0Game = { OTPImport.otpGame false with name := "OTP0" } := rfl

/-- The generated game and the hand-written game at the same message bit lower to
one `SPComp Bool`. `lowerGame` reads a game's procedures, body and result
expression, and the two games differ only in the source name they carry. -/
theorem lowerClosedGame_otp0Game :
    lowerClosedGame Generated.otp0Game = lowerClosedGame (OTPImport.otpGame false) :=
  rfl

/-- Zero distinguishing advantage between the generated game and the hand-written
game at the other message bit, from `OTPImport.otpImport_advantage_zero` along
`lowerClosedGame_otp0Game`. -/
theorem generated_otp0_advantage_zero (A : Bool → SPComp Bool) :
    AdvantageA (lowerClosedGame Generated.otp0Game)
      (lowerClosedGame (OTPImport.otpGame true)) A = 0 := by
  rw [lowerClosedGame_otp0Game]
  exact OTPImport.otpImport_advantage_zero false true A

/-! ## The elaborated module matches the decoded module's shape -/

-- The module name, the declared names, and the absence of globals.
#guard Generated.otpArgModule.name == "OTPArg"
#guard Generated.otpArgModule.interface.names == ["main", "enc"]
#guard Generated.otpArgModule.globals.isEmpty

-- `enc` is declared from `bool` to `bool`.
#guard Generated.otpArgModule.interface.sig "enc" == { arg := .bool, res := .bool }

-- `main` calls `enc` at the exporter's qualified name, binding the result to `r`.
#guard (match Generated.otpArgModule.procs "main" with
        | { param := _, body := [.callProc "Top.OTPArg./enc" _ _ "r"], ret := _ } => true
        | _ => false)

-- The body of `enc` is the sample, then the conditional whose branches assign `c`,
-- and its formal parameter is the source name `m`.
#guard (match Generated.otpArgModule.procs "enc" with
        | { param := "m",
            body := [.sample .bool "k",
                     .ite (.var .bool "m")
                       [.assign .bool "c" (.bxor (.var .bool "k") (.lit true))]
                       [.assign .bool "c" (.var .bool "k")]],
            ret := _ } => true
        | _ => false)

/-! ## The elaborated functor matches the decoded functor's shape -/

#guard Generated.negFunctor.name == "Neg"
#guard Generated.negFunctor.paramName == "P"
#guard Generated.negFunctor.paramInterface.names == ["guess"]
#guard Generated.negFunctor.paramInterface.sig "guess" == { arg := .bool, res := .bool }
#guard Generated.negFunctor.body.interface.names == ["guess"]
#guard Generated.negFunctor.body.globals.isEmpty

-- The body calls the parameter by the cross-path the exporter writes, at the
-- signature the module type declares.
#guard (match Generated.negFunctor.body.procs "guess" with
        | { param := "c", body := [.callProc "P./guess" s _ "b"], ret := _ } =>
          s == { arg := .bool, res := .bool }
        | _ => false)

/-! ## Per-constructor round trip

The one-time-pad export reaches nine of the AST's constructors. The checks below
cover the rest, one constructor at a time: each declaration's body is written
character for character as the emitter prints it, and the `#guard` beside it checks
that the emitter does print exactly that text. Elaborating the declaration is the
other direction — the text is a term denoting the value the emitter was given — so
the pair is a round trip at that constructor. -/

/-- A literal at a finite scalar type. -/
private def covFinLit : EcExpr (.fin 2) := (EcExpr.lit (t := (EcTy.fin 2)) (1 : Fin 3))
#guard emitExpr covFinLit == "(EcExpr.lit (t := (EcTy.fin 2)) (1 : Fin 3))"

/-- A literal at a product type. -/
private def covProdLit : EcExpr (.prod .bool .unit) :=
  (EcExpr.lit (t := (EcTy.prod EcTy.bool EcTy.unit)) (true, ()))
#guard emitExpr covProdLit == "(EcExpr.lit (t := (EcTy.prod EcTy.bool EcTy.unit)) (true, ()))"

/-- A literal at the unit type. -/
private def covUnitLit : EcExpr .unit := (EcExpr.lit (t := EcTy.unit) ())
#guard emitExpr covUnitLit == "(EcExpr.lit (t := EcTy.unit) ())"

/-- Boolean negation under conjunction. -/
private def covBand : EcExpr .bool :=
  (EcExpr.band (EcExpr.bnot (EcExpr.var EcTy.bool "b")) (EcExpr.var EcTy.bool "c"))
#guard emitExpr covBand ==
  "(EcExpr.band (EcExpr.bnot (EcExpr.var EcTy.bool \"b\")) (EcExpr.var EcTy.bool \"c\"))"

/-- Equality at a finite scalar type. -/
private def covBeq : EcExpr .bool :=
  (EcExpr.beq (t := (EcTy.fin 2)) (EcExpr.var (EcTy.fin 2) "x") (EcExpr.var (EcTy.fin 2) "y"))
#guard emitExpr covBeq ==
  "(EcExpr.beq (t := (EcTy.fin 2)) (EcExpr.var (EcTy.fin 2) \"x\") (EcExpr.var (EcTy.fin 2) \"y\"))"

/-- Pair construction. -/
private def covPair : EcExpr (.prod .bool (.fin 2)) :=
  (EcExpr.pair (a := EcTy.bool) (b := (EcTy.fin 2)) (EcExpr.var EcTy.bool "b") (EcExpr.var (EcTy.fin 2) "x"))
#guard emitExpr covPair ==
  "(EcExpr.pair (a := EcTy.bool) (b := (EcTy.fin 2)) (EcExpr.var EcTy.bool \"b\") (EcExpr.var (EcTy.fin 2) \"x\"))"

/-- First projection. -/
private def covFst : EcExpr .bool :=
  (EcExpr.fst (a := EcTy.bool) (b := EcTy.unit) (EcExpr.var (EcTy.prod EcTy.bool EcTy.unit) "p"))
#guard emitExpr covFst ==
  "(EcExpr.fst (a := EcTy.bool) (b := EcTy.unit) (EcExpr.var (EcTy.prod EcTy.bool EcTy.unit) \"p\"))"

/-- Second projection. -/
private def covSnd : EcExpr .unit :=
  (EcExpr.snd (a := EcTy.bool) (b := EcTy.unit) (EcExpr.var (EcTy.prod EcTy.bool EcTy.unit) "p"))
#guard emitExpr covSnd ==
  "(EcExpr.snd (a := EcTy.bool) (b := EcTy.unit) (EcExpr.var (EcTy.prod EcTy.bool EcTy.unit) \"p\"))"

/-- Addition at a finite scalar type. -/
private def covFinAdd : EcExpr (.fin 2) :=
  (EcExpr.finAdd (n := 2) (EcExpr.var (EcTy.fin 2) "x") (EcExpr.var (EcTy.fin 2) "y"))
#guard emitExpr covFinAdd ==
  "(EcExpr.finAdd (n := 2) (EcExpr.var (EcTy.fin 2) \"x\") (EcExpr.var (EcTy.fin 2) \"y\"))"

/-- A sample at a finite scalar type. -/
private def covSample : EcStmt := (EcStmt.sample (EcTy.fin 2) "x")
#guard emitStmt covSample == "(EcStmt.sample (EcTy.fin 2) \"x\")"

/-- A global read. -/
private def covLoad : EcStmt := (EcStmt.load (EcGlobal.mk "Top.M.g" 3 EcTy.bool) "b")
#guard emitStmt covLoad == "(EcStmt.load (EcGlobal.mk \"Top.M.g\" 3 EcTy.bool) \"b\")"

/-- A global write. -/
private def covStore : EcStmt :=
  (EcStmt.store (EcGlobal.mk "Top.M.g" 3 EcTy.bool) (EcExpr.var EcTy.bool "b"))
#guard emitStmt covStore ==
  "(EcStmt.store (EcGlobal.mk \"Top.M.g\" 3 EcTy.bool) (EcExpr.var EcTy.bool \"b\"))"

/-- A bounded loop. -/
private def covForN : EcStmt := (EcStmt.forN 4 [(EcStmt.sample EcTy.bool "b")])
#guard emitStmt covForN == "(EcStmt.forN 4 [(EcStmt.sample EcTy.bool \"b\")])"

/-- A sample from the uniform distribution expression. -/
private def covSampleUniform : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.uniform EcTy.bool))
#guard emitStmt covSampleUniform ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.uniform EcTy.bool))"

/-- A sample from a point mass. -/
private def covSamplePoint : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.point (t := EcTy.bool) (EcExpr.var EcTy.bool "y")))
#guard emitStmt covSamplePoint ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.point (t := EcTy.bool) " ++
    "(EcExpr.var EcTy.bool \"y\")))"

/-- A sample from a pushforward. -/
private def covSampleMap : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.map (a := EcTy.bool) (b := EcTy.bool) (EcDistr.uniform EcTy.bool) "c" (EcExpr.bnot (EcExpr.var EcTy.bool "c"))))
#guard emitStmt covSampleMap ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.map (a := EcTy.bool) (b := EcTy.bool) " ++
    "(EcDistr.uniform EcTy.bool) \"c\" (EcExpr.bnot (EcExpr.var EcTy.bool \"c\"))))"

/-- A sample from a conditioned distribution. -/
private def covSampleCond : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.cond (t := EcTy.bool) (EcDistr.uniform EcTy.bool) "c" (EcExpr.var EcTy.bool "c")))
#guard emitStmt covSampleCond ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.cond (t := EcTy.bool) " ++
    "(EcDistr.uniform EcTy.bool) \"c\" (EcExpr.var EcTy.bool \"c\")))"

/-- A sample from a pushforward under a stamped binder, which is what the binder
of a decoded distribution operator is. A program variable carries no stamp and
prints as its source name; a stamped identifier prints with both fields. -/
private def covSampleMapStamped : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.map (a := EcTy.bool) (b := EcTy.bool) (EcDistr.uniform EcTy.bool) (EcVarId.mk "c" (some 3)) (EcExpr.bnot (EcExpr.var EcTy.bool (EcVarId.mk "c" (some 3))))))
#guard emitStmt covSampleMapStamped ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.map (a := EcTy.bool) (b := EcTy.bool) " ++
    "(EcDistr.uniform EcTy.bool) (EcVarId.mk \"c\" (some 3)) " ++
    "(EcExpr.bnot (EcExpr.var EcTy.bool (EcVarId.mk \"c\" (some 3))))))"

/-- A sample from a bind. -/
private def covSampleLet : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.letD (a := EcTy.bool) (b := EcTy.bool) (EcDistr.uniform EcTy.bool) "c" (EcDistr.point (t := EcTy.bool) (EcExpr.var EcTy.bool "c"))))
#guard emitStmt covSampleLet ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.letD (a := EcTy.bool) (b := EcTy.bool) " ++
    "(EcDistr.uniform EcTy.bool) \"c\" (EcDistr.point (t := EcTy.bool) " ++
    "(EcExpr.var EcTy.bool \"c\"))))"

/-- A sample from an independent product. -/
private def covSampleProd : EcStmt :=
  (EcStmt.sampleD (EcTy.prod EcTy.bool EcTy.bool) "p" (EcDistr.prod (EcDistr.uniform EcTy.bool) (EcDistr.uniform EcTy.bool)))
#guard emitStmt covSampleProd ==
  "(EcStmt.sampleD (EcTy.prod EcTy.bool EcTy.bool) \"p\" (EcDistr.prod " ++
    "(EcDistr.uniform EcTy.bool) (EcDistr.uniform EcTy.bool)))"

/-- A sample from a rescaled distribution. -/
private def covSampleScale : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.scale (t := EcTy.bool) (EcDistr.uniform EcTy.bool)))
#guard emitStmt covSampleScale ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.scale (t := EcTy.bool) " ++
    "(EcDistr.uniform EcTy.bool)))"

/-- A sample from a restricted distribution. -/
private def covSampleRestrict : EcStmt :=
  (EcStmt.sampleD EcTy.bool "b" (EcDistr.restrict (t := EcTy.bool) (EcDistr.uniform EcTy.bool) "c" (EcExpr.var EcTy.bool "c")))
#guard emitStmt covSampleRestrict ==
  "(EcStmt.sampleD EcTy.bool \"b\" (EcDistr.restrict (t := EcTy.bool) " ++
    "(EcDistr.uniform EcTy.bool) \"c\" (EcExpr.var EcTy.bool \"c\")))"

/-- An argument-free intra-game call. -/
private def covCall : EcStmt := (EcStmt.call "aux")
#guard emitStmt covCall == "(EcStmt.call \"aux\")"

/-- Integer addition. -/
private def covIntAdd : EcExpr .int :=
  (EcExpr.intAdd (EcExpr.var EcTy.int "i") (EcExpr.lit (t := EcTy.int) (1 : Int)))
#guard emitExpr covIntAdd ==
  "(EcExpr.intAdd (EcExpr.var EcTy.int \"i\") (EcExpr.lit (t := EcTy.int) (1 : Int)))"

/-- Integer comparison. -/
private def covIntLe : EcExpr .bool :=
  (EcExpr.intLe (EcExpr.var EcTy.int "i") (EcExpr.var EcTy.int "j"))
#guard emitExpr covIntLe ==
  "(EcExpr.intLe (EcExpr.var EcTy.int \"i\") (EcExpr.var EcTy.int \"j\"))"

/-- A finite-map literal. -/
private def covMapLit : EcExpr (.map .bool .int) :=
  (EcExpr.lit (t := (EcTy.map EcTy.bool EcTy.int)) ([(true, (1 : Int))] : (EcTy.map EcTy.bool EcTy.int).interp))
#guard emitExpr covMapLit ==
  "(EcExpr.lit (t := (EcTy.map EcTy.bool EcTy.int)) ([(true, (1 : Int))] : " ++
    "(EcTy.map EcTy.bool EcTy.int).interp))"

/-- Binding a key in a finite map. -/
private def covMapSet : EcExpr (.map .bool .int) :=
  (EcExpr.mapSet (EcExpr.var (EcTy.map EcTy.bool EcTy.int) "m") (EcExpr.var EcTy.bool "k") (EcExpr.var EcTy.int "v"))
#guard emitExpr covMapSet ==
  "(EcExpr.mapSet (EcExpr.var (EcTy.map EcTy.bool EcTy.int) \"m\") " ++
    "(EcExpr.var EcTy.bool \"k\") (EcExpr.var EcTy.int \"v\"))"

/-- Membership in a finite map. -/
private def covMapMem : EcExpr .bool :=
  (EcExpr.mapMem (a := EcTy.bool) (b := EcTy.int) (EcExpr.var (EcTy.map EcTy.bool EcTy.int) "m") (EcExpr.var EcTy.bool "k"))
#guard emitExpr covMapMem ==
  "(EcExpr.mapMem (a := EcTy.bool) (b := EcTy.int) " ++
    "(EcExpr.var (EcTy.map EcTy.bool EcTy.int) \"m\") (EcExpr.var EcTy.bool \"k\"))"

/-- Lookup with a default in a finite map. -/
private def covMapGetD : EcExpr .int :=
  (EcExpr.mapGetD (a := EcTy.bool) (b := EcTy.int) (EcExpr.var (EcTy.map EcTy.bool EcTy.int) "m") (EcExpr.var EcTy.bool "k") (EcExpr.lit (t := EcTy.int) (0 : Int)))
#guard emitExpr covMapGetD ==
  "(EcExpr.mapGetD (a := EcTy.bool) (b := EcTy.int) " ++
    "(EcExpr.var (EcTy.map EcTy.bool EcTy.int) \"m\") (EcExpr.var EcTy.bool \"k\") " ++
    "(EcExpr.lit (t := EcTy.int) (0 : Int)))"

/-- A read of a global at a non-finite code. -/
private def covLoadMap : EcStmt :=
  (EcStmt.load (EcGlobal.mk "Top.M.log" 4 (EcTy.map EcTy.bool EcTy.int)) "m")
#guard emitStmt covLoadMap ==
  "(EcStmt.load (EcGlobal.mk \"Top.M.log\" 4 (EcTy.map EcTy.bool EcTy.int)) \"m\")"

/-- A write of a global at a non-finite code. -/
private def covStoreMap : EcStmt :=
  (EcStmt.store (EcGlobal.mk "Top.M.log" 4 (EcTy.map EcTy.bool EcTy.int)) (EcExpr.var (EcTy.map EcTy.bool EcTy.int) "m"))
#guard emitStmt covStoreMap ==
  "(EcStmt.store (EcGlobal.mk \"Top.M.log\" 4 (EcTy.map EcTy.bool EcTy.int)) " ++
    "(EcExpr.var (EcTy.map EcTy.bool EcTy.int) \"m\"))"

/-! ## The printed interface elaborates to the printed interface -/

/-- The interface of `Generated.otpArgModule`, written as `emitInterface` prints
it. -/
def otpArgInterface : EcInterface :=
  (interfaceOfSigs [("main", (EcSig.mk EcTy.unit EcTy.bool)),
                    ("enc", (EcSig.mk EcTy.bool EcTy.bool))])

-- The text `emitInterface` prints for that interface is the term above.
#guard emitInterface Generated.otpArgModule.interface ==
  "(interfaceOfSigs [(\"main\", (EcSig.mk EcTy.unit EcTy.bool)), " ++
    "(\"enc\", (EcSig.mk EcTy.bool EcTy.bool))])"

-- The elaborated term declares the same names at the same signatures.
#guard otpArgInterface.names == Generated.otpArgModule.interface.names
#guard otpArgInterface.names.all (fun p =>
  otpArgInterface.sig p == Generated.otpArgModule.interface.sig p)

end CatCrypt.Crypto.EasyCryptImport
