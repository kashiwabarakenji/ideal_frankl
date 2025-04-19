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
lean_lib rooted where --この名前はそれほど重要でなく、プロジェクト名に合わせる必要もない。
  roots:= #[`rooted.GeneralLemma, `rooted.Dominant, `rooted.Parallel, `rooted.ClosureOperator, `rooted.RootedImplication, `rooted.RootedFrankl, `rooted.StemSizeOne,`rooted.Superior, `rooted.FranklHyperedge, `rooted.CommonDefinition, `rooted.FamilyLemma, `rooted.RootedSets, `rooted.RootedCircuits, `rooted.Bridge, `rooted.ClosureMinors, `rooted.Preorder, `rooted.functionalCommon, `rooted.functionalTreePartialorder, `rooted.functionalTreePreorder, `rooted.functionalTreeIdeal, `rooted.functionalSPO,`rooted.functionalSPO2,`rooted.functionalIdealrare ] --この名前は、lake buildされるターゲットになる。importと同じ名前になる。
  srcDir := "." -- ピリオドにすると、プロジェクトフォルダのトップからになる。
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @ "v4.17.0" -- "v4.8.0"
require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.17.0" --"v1.6.0"

--mathlibのバージョンは、lean --versionで表示されるものに合わせる必要。
-- https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
---emacs lean-toolchain
-- leanのバージョンはelan install leanprover/lean4:4.8.0など。arm64用であることを確認。
-- elan toolchain install leanprover/lean4:4.8.0
-- elan default leanprover/lean4:4.8.0
-- lean --versionで確認。これは、toolchanのものが表示されるみたい。なければここでダウンロードされる。
-- require mathlib from git "のバージョンを合わせる。
-- lake clean;lake update;lake build
-- elan override set leanprover/lean4:4.16.0
