# フランクルの予想のLean 4によるアプローチ

フランクルの予想は、組み合わせ論の未解決問題である。有限台集合上の共通部分で閉じた集合族で全体集合と空集合を持つ物を考える。このとき、必ずrareな頂点を持つという予想がフランクルの予想である。rareな頂点とは、頂点を通るhyperedge(集合族の要素)の個数が、半分以下となるというものである。この予想は、未だに未解決ではあるが、いくつかの簡単なクラスでは成り立つことが知られている。そのひとつがIdeal集合族と呼ばれるクラスである。Ideal集合族は、空集合と全体集合を持ち、全体集合以外のhyperedgeは、部分集合で閉じているような集合族である。

一方、頂点全体の平均的な次数がrare(hyperedgeの大きさの合計が頂点数とhyperedgeの数の積の半分以下である場合)である集合族は、rareな頂点を持つことは簡単にわかる。Ideal集合族が平均的にrareであるかどうかは、一見簡単に証明できそうであるが、実際に示しそうとするとそれほど簡単ではない。今回は、そのことを(人力で)証明し、Lean 4でその証明を記述して、正しいことを検証してみた。このGitHUBリポジトリは、そのLean 4による証明を公開したものである。

定理の証明がややこしいと言っても、自然言語で他人に説明すると10分ぐらいで証明を説明し終わると思われる。しかし、Lean 4で証明を記述すると、5000行ぐらい必要だった。また、Lean 4の初心者の私には、3ヶ月ぐらいの日数がかかった。証明の作成において、支援ツールとして、ChatGPT PlusとLean CopilotとGitHUB Copilotを利用した。これらは、簡単な自動証明を行なってくれるツールとも言える。たとえば、ChatGPTは、人間が自然言語で与えた証明をLean 4に翻訳したものを提案してくれる。ChatGPTとGitHUBの提案するコードは、Lean 3の文法やMathlib 3の定理を含んだものが多かったので、そのまま、採用とはならず、かなりの程度、修正する必要があった。とりあえず、証明が検証を通ることを目指したので、作成した証明は、必ずしも人間がわかりやすいものになっていない部分もある。今後も継続して、リファクタリングを行い、可読性を上げようと思う。

srcのidealのフォルダに今回の定理のLeanの証明が格納されている。
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

--イデアル集合族
structure IdealFamily (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α :=
(empty_mem : sets ∅)  -- 空集合が含まれる
(univ_mem : sets ground)  -- 全体集合が含まれる
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

--大きさnで標準化次数和が負かどうか。
def P (x:Nat) : Prop := x ≥ 2  ∧ ∀ (F: IdealFamily (Fin x)), F.ground.card = x → normalized_degree_sum F.toSetFamily ≤ 0
```

### Ideal集合族のマイナー操作

集合族に対して、頂点vによるcontractionは、vを含むhyperedge Hを動かして、H-vを集めた集合族である。
{v}がhyperedgeであることに、Ideal集合族のcontractionはまたIdeal集合族になる。

集合族に対して、頂点vによるdeletionは、vを含まないhyperedgeを全て集めてきたものである。
ただし、deletion後の集合族は、部分集合では閉じているが、全体集合を持つとは限らないので、ground-vがhyperedgeでない場合は、ground-vを追加してあげることで、Ideal集合族になる。

集合族に対して、traceとは、hyperedge Hを動かして、H-vを集めたものである。ideal集合族のtraceは、またideal集合族になる。

### 定理の証明

Ideal集合族が平均rareになるという言明の証明の概略を述べる。

基本的には、台集合の大きさに関する帰納法を用いる。

ベースケースとしては、n = 2の場合を証明した。IdealMain.leanにそのbasecaseの言明がある。

以下は、帰納的ステップの証明である。つまり、台集合がnの場合に言明が成り立つことを仮定する。
この時に、台集合の大きさがn+1のIdeal集合族に対して、言明が成り立つことを証明する。つまり、標準化次数和((hyperedgeの大きさの合計)*2-(台集合の大きさ)*(hyperedge数))が負であることを証明すれば良い。

まず、rare vetexを持つことを証明する。その頂点をvとする。

groundを台集合として、ground-vがhyperedgeかどうかと、{v}がhyperedgeかどうかで、4通りに場合分けして考える。

それぞれに対して、hyperedgeの数と、hyperedgeの大きさの合計を、vをdeletionした集合族、vをcontractionした集合族のhyperedgeの数やhyperedgeの大きさで表すことができる。

Ideal集合族の1頂点をcontractionした集合族は、またIdeal集合族になることが証明できる。ただし、{v}がhyperedgeでないとcontractionしたものが空集合を持たないので、{v}がhyperedgeになるかどうかで場合分けして考える必要がある。{v}がhyperedgeでない時は、vの次数が1になる。この時は、contractionではなく、vをtraceして考えるとidealになる。
また、Ideal集合族の1頂点をdeletionした集合族は、またIdeal集合族になる。しかし、ground-vがhyperedgeでないときは、deletionにより、全体集合がなくなるので、追加する必要がある。