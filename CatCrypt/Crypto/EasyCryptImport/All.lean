/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Ty
import CatCrypt.Crypto.EasyCryptImport.Ast
import CatCrypt.Crypto.EasyCryptImport.Json
import CatCrypt.Crypto.EasyCryptImport.Modules
import CatCrypt.Crypto.EasyCryptImport.Lower
import CatCrypt.Crypto.EasyCryptImport.FunctorN
import CatCrypt.Crypto.EasyCryptImport.Restrictions
import CatCrypt.Crypto.EasyCryptImport.Form
import CatCrypt.Crypto.EasyCryptImport.FormJson
import CatCrypt.Crypto.EasyCryptImport.FormToProp
import CatCrypt.Crypto.EasyCryptImport.Emit
import CatCrypt.Crypto.EasyCryptImport.EmitMain
import CatCrypt.Crypto.EasyCryptImport.EmitCheck
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPImport
import CatCrypt.Crypto.EasyCryptImport.Examples.QFoldImport
import CatCrypt.Crypto.EasyCryptImport.Examples.ModuleImport
import CatCrypt.Crypto.EasyCryptImport.Examples.FormImport
import CatCrypt.Crypto.EasyCryptImport.Examples.OTPEquivImport
import CatCrypt.Crypto.EasyCryptImport.Examples.HoareImport
import CatCrypt.Crypto.EasyCryptImport.Examples.RestrictedImport
import CatCrypt.Crypto.EasyCryptImport.Examples.AdversaryEquivImport
import CatCrypt.Crypto.EasyCryptImport.Examples.FunctorGlobImport
import CatCrypt.Crypto.EasyCryptImport.Examples.FunctorImport
import CatCrypt.Crypto.EasyCryptImport.Examples.Functor2Import
import CatCrypt.Crypto.EasyCryptImport.Examples.RandomOracleImport
import CatCrypt.Crypto.EasyCryptImport.Examples.NonUniformImport
import CatCrypt.Crypto.EasyCryptImport.Examples.DistrBindImport

/-!
# EasyCrypt importer: import manifest

This module forces every module of the EasyCrypt importer, including the worked
examples, the emitter, and the generated files. The examples have no importer of
their own, so building this module is what keeps them from rotting when the AST,
the lowering, or the CatCrypt core they target changes. Building it also runs the
`#guard` checks of `Json.lean`, `FormJson.lean`, `EmitCheck.lean`,
`Examples/OTPEquivImport.lean`, `Examples/HoareImport.lean`,
`Examples/RestrictedImport.lean`, `Examples/AdversaryEquivImport.lean`,
`Examples/FunctorGlobImport.lean`, `Examples/FunctorImport.lean`,
`Examples/Functor2Import.lean` and `Examples/DistrBindImport.lean`, which decode
the exporter fixtures `otp.expected.json`, `forms.expected.json`,
`otpequiv.expected.json`, `hoare.expected.json`, `restr.expected.json`,
`advequiv.expected.json`, `globimg.expected.json`, `functor.expected.json`,
`functor2.expected.json`, `nonunif.expected.json` and `distrbind.expected.json` and
compare the result against the generated files under `Examples/` and against the
ASTs the examples state.
-/
