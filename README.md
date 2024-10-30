# フランクルの予想のLean 4によるアプローチ -- Ideal集合族のケース --

## 概要
フランクルの予想は、組合せ論の長年の未解決問題である。有限台集合上の共通部分で閉じた集合族で全体集合と空集合を持つものを考える。このような集合族は、必ずrareな頂点を持つという予想がフランクルの予想である。rareな頂点とは、その頂点を通るhyperedge(集合族の要素)の個数が、hyperedge全体の数の半分以下となるというものである。この予想は、未だに未解決ではあるが、いくつかの簡単なクラスでは成り立つことが知られている。そのひとつがIdeal集合族と呼ばれるクラスである。Ideal集合族は、空集合と全体集合を持ち、全体集合以外のhyperedgeは、部分集合で閉じているような集合族である。Ideal集合族は、共通部分で閉じていることが簡単にわかる。

一方、頂点全体の平均的な次数がrare(hyperedgeの大きさの合計が頂点数とhyperedgeの数の積の半分以下である場合)である集合族は、rareな頂点を持つことは簡単にわかる。Ideal集合族が平均的にrare (((hyperedgeの大きさの合計)*2-(台集合の大きさ)*(hyperedge数))が負)であるかどうかは、一見簡単に証明できそうであるが、実際に示しそうとするとそれほど簡単ではない。今回は、この言明を(まず人力で)証明し、Lean 4でその証明を記述して、正しいことを検証してみた。このGitHUBリポジトリは、その言明に対するLean 4による証明を公開したものである。Lean 4は、数学の言明や証明を形式的に記述できて、その数学的な正しさを厳密に保証してくれるシステムである。

## 証明の作成について

定理の証明がややこしいと言っても、自然言語で他人に説明すると10分ぐらいで証明を説明し終わると思われる。しかし、Lean 4で証明を記述すると、5000行ぐらい必要だった。また、Lean 4の初心者の私には、3ヶ月ぐらいの日数がかかった。Lean 4の証明の作成において、支援ツールとして、ChatGPT PlusとLean CopilotとGitHUB Copilotを利用した。これらは、簡単な自動証明を行なってくれるツールとも言える。たとえば、ChatGPTは、人間が自然言語で与えた証明をLean 4に翻訳したものを提案してくれる。ChatGPTとGitHUBの提案するコードは、古いバージョンであるLean 3の文法やMathlib 3の定理を含んだものが多かったので、そのまま、採用とはいかず、かなりの程度、人力で修正する必要があった。Lean Copilotは、Leanのバージョンにあった正しいコードを提案してくれるが、複雑な証明はできない。とりあえず、証明が検証を通ることを目指したので、作成した証明は、必ずしも人間がわかりやすいものになっていない部分もある。今後も継続して、コードのリファクタリングを行い、可読性を上げようと思う。

## 主要な定理と定義について

リポジトリのidealのフォルダに今回の定理のLeanの証明が格納されている。
IdealMain.leanの中の最後の

```
theorem P_all (x : Nat) (hx : x ≥ 2) : P x
```

の部分がメインの結果の言明である。P nが台集合の大きさがnの任意のideal集合族に対して、平均rareであることを示している。

主要な定義を述べる。

```
--集合族
structure SetFamily (α : Type) [DecidableEq α] [Fintype α] :=
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  [fintype_ground : Fintype ground]

-- hyperedgeがが共通部分に対して閉じていることを定義
def is_closed_under_intersection (sf : SetFamily α) : Prop :=
  ∀ (A B : Finset α), sf.sets A → sf.sets B → sf.sets (A ∩ B)

-- 頂点がrareであることを定義
def is_rare (sf : SetFamily α) (v : α)  [DecidablePred sf.sets]  : Prop :=
  2 * degree sf v ≤ number_of_hyperedges sf

--イデアル集合族
structure IdealFamily (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α :=
(has_empty : sets ∅)  -- 空集合が含まれる
(has_ground : sets ground)  -- 全体集合が含まれる
(down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

--hyperedge数の大きさの合計
def total_size_of_hyperedges (F : SetFamily α)  [DecidablePred F.sets] : ℕ :=
  let all_sets := (Finset.powerset F.ground).filter F.sets
  all_sets.sum Finset.card

--hyperedge数
def number_of_hyperedges (F : SetFamily α) [DecidablePred F.sets] : ℕ :=
  ((Finset.powerset F.ground).filter F.sets).card
  --let all_sets := (Finset.powerset F.ground).filter F.sets
  --all_sets.card

--頂点の次数
noncomputable def degree (sf : SetFamily α) (v : α) : ℕ :=
  Finset.card (Finset.filter (λ s => sf.sets s = true ∧ v ∈ s) (sf.ground.powerset))

--標準化次数和=total_size * 2 - num_sets * base_set_size
noncomputable def normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) : ℤ :=
  let total_size := (total_size_of_hyperedges F: ℤ)
  let num_sets := (number_of_hyperedges F: ℤ)
  let base_set_size := (F.ground.card: ℤ)
  total_size * 2 - num_sets * base_set_size

--大きさnで標準化次数和が負かどうかの述語。
def P (x:Nat) : Prop := x ≥ 2  ∧ ∀ (F: IdealFamily (Fin x)), F.ground.card = x → normalized_degree_sum F.toSetFamily ≤ 0
```

## Ideal集合族のマイナー操作

ideal集合族から1点台集合が小さいideal集合族を作る操作には、deletionとcontractionとtraceの3種類がある。

集合族に対して、頂点vによるcontractionは、vを含むhyperedge Hを動かして、H-vを集めた集合族である。contractionにより、downward-closed性は保存される。
{v}がhyperedgeであるときに、contractionは空集合を持つので、Ideal集合族のcontractionはまたIdeal集合族になる。

集合族に対して、頂点vによるdeletionは、vを含まないhyperedgeを全て集めてきたものである。
ただし、deletion後の集合族は、部分集合では閉じているが、全体集合を持つとは限らないので、ground-vがhyperedgeでない場合は、ground-vを追加してあげることで、Ideal集合族になる。

集合族に対して、traceとは、hyperedge Hを動かして、H-vを集めたものである。ideal集合族のtraceは、またideal集合族になる。

## 定理の証明

Ideal集合族は必ず、平均rareになるという言明(P)がこの研究の主定理となる。
この定理の証明の概略を述べる。

基本的には、台集合の大きさに関する帰納法を用いる。

ベースケースとしては、n = 2の場合を証明した(P 2)。IdealMain.leanにそのbasecaseの言明(theorem basecase)がある。

以下は、帰納的ステップの証明である。つまり、台集合がnの場合に言明が成り立つことを仮定する。
この時に、台集合の大きさがn+1のIdeal集合族に対して、言明が成り立つことを証明する。つまり、標準化次数和((hyperedgeの大きさの合計)*2-(台集合の大きさ)*(hyperedge数))が負であることを証明すれば良い。(IdealMain.leanのinductive_step)

まず、rare vetexを持つことを証明する(IdealRare.leanのtheorem ideal_version_of_frankl_conjecture)。その頂点をvとする。

groundを台集合として、ground-vがhyperedgeかどうかと、{v}がhyperedgeかどうかで、4通りに場合分けして考える。

それぞれに対して、hyperedgeの数と、hyperedgeの大きさの合計を、vをdeletionした集合族、vをcontractionした集合族のhyperedgeの数やhyperedgeの大きさで表すことができる。

Ideal集合族の1頂点をcontractionした集合族は、またIdeal集合族になることが証明できる。ただし、{v}がhyperedgeでないとcontractionしたものが空集合を持たないので、{v}がhyperedgeになるかどうかで場合分けして考える必要がある。{v}がhyperedgeでない時は、vの次数が1になる。この時は、contractionではなく、vをtraceして考えるとidealになる。
また、Ideal集合族の1頂点をdeletionした集合族は、またIdeal集合族になる。しかし、ground-vがhyperedgeでないときは、deletionにより、全体集合がなくなるので、追加する必要がある。

## 各ケースの補題

### {v}がhyperedgeのときのhyperedge数の計算
{v}がhyperedgeのときのhyperedge数の計算は、IdealNumbers.leanの中のtheorem hyperedge_count_deletion_contraction_none_z (ground-vがhyperedgeでない場合)やtheorem hyperedge_count_deletion_contraction_have_z  (ground-vがhyperedgeである場合)などに記述されている。

hyperedgeの数は、deletionした集合族のhyperedgeの数と、contractionした集合族のhyperedgeの数から計算できる。
```
theorem hyperedge_count_deletion_contraction_have_z {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x}))(singleton_have: F.sets {x}) :
  ((number_of_hyperedges F.toSetFamily):ℤ) =
  ((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) +
  ((number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily) :ℤ)

theorem hyperedge_count_deletion_contraction_none_z {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (ground_v_none : ¬ F.sets (F.ground \ {x})) (singleton_have: F.sets {x}) :
  ((number_of_hyperedges F.toSetFamily):ℤ) + 1 =
  (number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily:ℤ)  +
  (number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily:ℤ) 
```

### {v}がhyperedgeのときのhyperedgeの和の計算
{v}がhyperedgeのときのhyperedgeの大きさの和の計算は、IdealSum.leanの中のtheoremで、deletionやcontractionした集合族のhyperedgeの大きさの和から計算できる。

```
theorem hyperedge_totalsize_deletion_contraction_have_z {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x})) :
  ((total_size_of_hyperedges F.toSetFamily):ℤ) =
  ((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)   +
  ((total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ)  + ((degree F.toSetFamily x):ℤ)

theorem hyperedge_totalsize_deletion_contraction_none {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (ground_v_none : ¬ F.sets (F.ground \ {x})) (singleton_have : F.sets {x}) :
  ((total_size_of_hyperedges F.toSetFamily):ℤ) + ((F.ground.card:ℤ) - 1)=
  (total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily:ℤ)  +
  (total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two):ℤ) + ((degree F.toSetFamily x):ℤ)
```
### {v}がhyperedgeのときの標準化次数和の計算
hyperedge数と、hyperedgeの大きさの和の関係から、標準化次数和は、contractionした集合族の標準化次数和とdeletionした集合族の標準化次数和から計算できる。
```
theorem hyperedge_average_have {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x})) (singleton_have : F.sets {x}) :
  normalized_degree_sum F.toSetFamily =
  normalized_degree_sum (idealdeletion F x hx ground_ge_two).toSetFamily  +
  normalized_degree_sum (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily
  +2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges F.toSetFamily):ℤ)

theorem hyperedge_average_none {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (ground_v_none : ¬ F.sets (F.ground \ {x})) (singleton_have : F.sets {x}) :
  normalized_degree_sum F.toSetFamily + (F.ground.card:ℤ)=
  normalized_degree_sum (idealdeletion F x hx ground_ge_two).toSetFamily  +
  normalized_degree_sum (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily
  + 2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges F.toSetFamily):ℤ) + 1 
```

### {v}がhyperedgeでないときの計算
{v}がhyperedgeでないideal集合族は、vの次数が1になる。このときは、vをtraceした集合族がideal集合族になることが示せる。
もともとの集合族のhyperedge数とtraceした集合族のhyperedge数の関係が、ground-vがhyperedgeの場合と、そうでない場合でそれぞれで計算できる。また、もともとの集合族のhyperedgeの大きさの和と、traceした集合族のhyperedgeの大きさの和の関係が、ground-vがhyperedgeの場合と、そうでない場合でそれぞれで計算できる。

そもそもground-vがhyperedgeで、{v}がhyperedgeでない場合は、Ideal集合族がnの大きさだけで決まるので、標準化次数和が計算できて、非負であることも確認できる。(IdealDegreeOne.lean)

{v}がhyperedgeでなくて、ground-vがhyperedgeでないときのケースは、IdealDegOneMain.leanにて議論されている。vをtraceした集合族は、hyperedge数は元の集合族と変わらずに、hyperedgeの大きさの和は元の集合族に比べて1少ない。帰納法の仮定より、traceした集合族で、標準化次数和が非負であることより、元の集合族でも標準化次数和が非負であることがわかる。

## leanのファイル構成

Idealフォルダにleanファイルがある。

- BasicDefinitions.lean  基本的な定義
- BasicLemmas.lean  基本的な補題

- IdealDegOneMain.lean {v}がhyperedgeでないときのメイン
- IdealDegreeOne.lean {v}がhyperedgeでないときの補題。さらにground-vがhyperedgeである場合も含む。
- IdealDeletion.lean  deletionとcontractionに関する定義や補題
- IdealTrace.lean  traceに関する定義や補題
- IdealNumbers.lean {v}がhyperedgeであるケースのhyperedgeの数に関する議論
- IdealSum.lean {v}がhyperedgeであるケースのhyperedgeの大きさの和に関する議論
- IdealSumBasic.lean IdealSumで使う補題を集めたもの。
- IdealRare.lean  Ideal集合族がrareな頂点を持つことを示している。
- IdealFin.lean 帰納法で(Fin n)と(Fin (n+1))を使ったのでその変換
- IntersectionClosed.lean 今回示した定理には直接関係ないが、Ideal集合族が共通部分で閉じていることの証明。

## leanの環境

使用したleanのバージョンは、leanprover/lean4:v4.11.0 である。
これは、証明作成時点で、Lean Copilotが利用できるバージョンを使用した。
lakefile.leanもLean Copilotがダウンロードされるように設定されている。
importでもLean Copilotを読み込んでいる。Lean Copilotに対応してない環境で取り込む際には注意が必要。
```
git clone https://github.com/kashiwabarakenji/ideal_frankl.git
```
でローカルなマシンに取り込むことができる。すでにelan等でleanがインストールされている環境であれば、
```
cd ideal_frankl
elan override set leanprover/lean4:v4.11.0
lake update
lake build
```
などのあとに、Lean 4の機能拡張がインストールされたVisual Studio Codeでideal_franklのフォルダを開けばよい。
適宜、start leanfileのボタンを押すとよい。

## TODO

- 平均rareであれば、rareな頂点が証明することのleanによる証明を作成する。
- READMEにおいて、自然言語による言明の証明を完結しているものにする。
- 証明のリファクタリングをする。変数名をわかりやすいものにする、コメントを整理するなど。
- READMEなどを英語にする。

