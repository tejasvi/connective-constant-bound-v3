import Lean

/-!
# Loading certificate data at build time

`load_cert_chunk name "path" hash` defines `name : String` (marked `noinline`) whose value is the
content of the file `path` (7-bit characters), after checking its 64-bit FNV-1a hash. The data enter the proof only
through these definitions: the checker's soundness does not depend on what they contain.
-/

open Lean Elab Command

namespace L38.Loader

/-- 64-bit FNV-1a hash of a byte array. -/
def fnv1a (b : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for x in b do
    h := (h ^^^ x.toUInt64) * 0x100000001b3
  return h

elab "load_cert_chunk " id:ident ppSpace path:str ppSpace h:num : command => do
  let bytes ← IO.FS.readBinFile path.getString
  let hv := fnv1a bytes
  unless hv.toNat == h.getNat do
    throwError "load_cert_chunk: hash mismatch for {path.getString}: file has {hv.toNat}"
  unless bytes.data.all (· < 128) do
    throwError "load_cert_chunk: {path.getString} contains a byte ≥ 128"
  let s := String.fromUTF8! bytes
  let decl := Declaration.defnDecl {
    name := id.getId, levelParams := [], type := mkConst ``String,
    value := mkStrLit s, hints := .opaque, safety := .safe }
  liftCoreM do
    addDecl decl
    -- never inline the literal into the code of other modules
    match Compiler.setInlineAttribute (← getEnv) id.getId .noinline with
    | .ok env => setEnv env
    | .error e => throwError e
    compileDecl decl

end L38.Loader
