/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.EasyCryptImport.Emit

/-!
# EasyCrypt import: the `ec2lean` entry point

`main` reads an exporter envelope from a JSON file, decodes one of its items with
`emitFromJson`, and writes the generated Lean module.

## Invocation

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  <export.json> <game|module|functor> <item-name> <decl-name> <out.lean>
```

`<out.lean>` of `-` prints to standard output. The exit code is `0` on success
and `1` on a JSON parse error, a decode error, or a bad argument list; a decode
error is written to standard error with the message the decoder produced.

The generated file declares `<decl-name>` in the namespace
`CatCrypt.Crypto.EasyCryptImport.Generated`; a module also declares
`<decl-name>Procs`, and a functor declares `<decl-name>Body` and
`<decl-name>BodyProcs`. Regenerating `Examples/OTPGenerated.lean`,
`Examples/OTPArgGenerated.lean` and `Examples/NegGenerated.lean`, which
`EmitCheck.lean` checks against the emitter's current output:

```
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  CatCrypt/Crypto/EasyCryptImport/otp.expected.json game OTP0 otp0Game \
  CatCrypt/Crypto/EasyCryptImport/Examples/OTPGenerated.lean
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  CatCrypt/Crypto/EasyCryptImport/otp.expected.json module OTPArg otpArgModule \
  CatCrypt/Crypto/EasyCryptImport/Examples/OTPArgGenerated.lean
lake env lean --run CatCrypt/Crypto/EasyCryptImport/EmitMain.lean \
  CatCrypt/Crypto/EasyCryptImport/functor.expected.json functor Neg negFunctor \
  CatCrypt/Crypto/EasyCryptImport/Examples/NegGenerated.lean
```

## Dispatch tables

The tables `main` decodes against are `ecPrelude`, the paths of EasyCrypt's
boolean and unit prelude. A source that uses a finite scalar type or a further
uniform distribution needs `DecodeTables.withFinType` / `.withUniformDistr`,
which no command line names: call `emitFromJson` from Lean with the extended
tables.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.EasyCryptImport

open Lean (Json)

/-- The usage message. -/
def emitUsage : String :=
  emitLines
    [ "usage: ec2lean <export.json> <game|module|functor> <item-name> <decl-name> <out.lean>",
      "       <out.lean> of '-' prints to standard output" ]

/-- Read an exporter envelope, decode the named item, and write the generated Lean
module. -/
def emitMain (args : List String) : IO UInt32 := do
  match args with
  | [inPath, kind, item, declName, outPath] =>
    let text ← IO.FS.readFile inPath
    match Json.parse text with
    | .error m =>
      IO.eprintln s!"ec2lean: {inPath}: {m}"
      return 1
    | .ok j =>
      match emitFromJson ecPrelude kind item declName j with
      | .error m =>
        IO.eprintln s!"ec2lean: {m}"
        return 1
      | .ok out =>
        if outPath == "-" then IO.print out else IO.FS.writeFile outPath out
        return 0
  | _ =>
    IO.eprint emitUsage
    return 1

end CatCrypt.Crypto.EasyCryptImport

/-- The entry point `lean --run` calls, which is `emitMain` on the command line's
arguments. -/
def main (args : List String) : IO UInt32 :=
  CatCrypt.Crypto.EasyCryptImport.emitMain args
