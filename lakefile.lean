import Lake
open Lake DSL

package Ideal {
  -- Settings applied to both builds and interactive editing
  --leanOptions := #[
  --  ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
 -- ]
  moreLinkArgs := #[
   "-L./.lake/packages/LeanCopilot/.lake/build/lib/",
   "-lctranslate2"
  ]
}
@[default_target]
lean_lib «Ideal» where
  --もともとの設定は以下で、src/Idealの下にファイルが置かれていた。
  --roots:= #[`Ideal]
  --srcDir := "src"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @ "v4.15.0" -- "v4.8.0"
require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.15.0" --"v1.6.0"

--mathlibのバージョンは、lean --versionで表示されるものに合わせる必要。
-- https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
---emacs lean-toolchain
-- leanのバージョンはelan install leanprover/lean4:4.8.0など。arm64用であることを確認。
-- elan toolchain install leanprover/lean4:4.8.0
-- elan default leanprover/lean4:4.8.0
-- lean --versionで確認。これは、toolchanのものが表示されるみたい。なければここでダウンロードされる。
-- require mathlib from git "のバージョンを合わせる。
-- lake clean;lake update;lake build
--v4.9.1には対応するものがない。ただしlake updateがとおる。
--v4.9.0にはv1.4.0が対応。ただし、lake updateが通らない。
