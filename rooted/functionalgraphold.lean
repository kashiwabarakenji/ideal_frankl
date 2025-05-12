import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--古いファイル。Setupを使って再構成したので、いらなくなった。消す。

--概略：function f:ground -> groundが定義する前順序を考える。この前順序に順序ideal全体を考えて、有限集合ground上の集合族と思う。
--この集合族が平均rareであることを示すのがメイン定理。
--⚪︎前順序
--groundを有限台集合とする。
--f:ground -> groundの関数が与えられると、v < f(v)というground上の2項関係が定義できて、これのtransitive closureを考えるとground上に前順序(preorder)が定義できる。
--vからみて、f(v)を親と呼ぶ。vとf(v)は異なると仮定しても同じ場合を許しても、似た問題になる。とりあえず異なると仮定して考えている。
--親を辿っていくと、頂点が循環することがある。その部分は、前順序において、同値な頂点集合ということになる。
--補題：functionが与えられると、前順序における頂点の同値類ができる。
--証明は一般的な前順序の議論でできる。すでに証明済み。
--補題：このように関数から定義された前順序において、任意のノードは、ちょうど上に1つの親にカバーされるか、極大ノード(a lt xならばx let a)である。
--証明は、数学的には前順序の定義から自明だが、lean 4の証明としては結構大変と思われる。親がたかだか一つであることは半順序のほうで使うので前順序のほうで証明する必要があるかを考えてもよい。
--⚪︎順序idealと平均rare
--順序idealとは、考えている前順序で、下に閉じている集合のことである。
--頂点集合上に前順序が与えられると順序idealの全体が決まる。これは集合族のhyperedgeと思って、平均rareになるかなどが議論できる。
--平均rareとは、(順序idealの大きさの和*2-順序idealの個数*台集合の大きさ)<=0のことである。
--○同値類上の半順序の定義
--補題：上のセッティングのもと、頂点の同値類上に半順序が定義できる。半順序関係の定義は、同値類Aから同値類Bに順序の大小があることを、任意の順序idealに対して、同値類Aを含んでいるならば同値類Bを含んでいるということと、定義する。
--この2項関係は、半順序の公理を満たす。
--補題：hyperedgeの集合の全体(=前順序の順序ideal全体)は、この半順序の順序idealに一致する。
--半順序は、前順序を直接使って定義するのではなく、集合族の含む含まれるの関係で定義していることに注意。以後では頂点をtraceすることによって、前順序では表しにくい半順序が出てくる。
--補題の補題：任意の順序idealに対して、同値類に含まれるか、disjointかのどちらかである。
--ある同値類に中途半端に交わると、同値類の定義に反することになる。
--補題：サイズが2以上の同値類は、半順序の極大要素に対応するところにしか出てこない。
--半順序の定義に戻って証明する。極大でないところに同値類があると、親が2つ出てくる頂点が存在することになる。
--前順序の極大要素はa < bならばb < aが成り立つものである。この性質を使って、同値類が極大でないところにあると、矛盾が生じる。
--補題: サイズ2以上の同値類の頂点は、rareな頂点になる。
--この補題の証明は、その同値類をhyperedge全体から含まないhyperedge全体への単射を作ることで可能。
--⚪︎パラレルな頂点のtraceと同値類上の半順序
--ground上に同値類が与えられていて、以下の条件を満たすとする。1. サイズ2以上の同値類は、半順序の極大な要素のみ。2. 半順序の親は、たかだか1つ。
--この半順序に対して、順序idealを考えて、hyperedgeと思って、集合族を考えることができる。
--同値な頂点(パラレルな頂点とも呼ぶ)のひとつをtraceすることにより、同一視していく方向性。
--補題: パラレルな頂点をtraceした場合、もとの前順序で大小関係があることと、traceした集合族での大小関係は一致する。ここでの大小関係は、hyperedgeがxを含んでいたらyも含むという関係。
--よって、パラレルな頂点をtraceした集合族もこれにより、前順序を定めることができる。サイズ2以上の同値類から同値な頂点をひとつtraceしても、半順序の親がたかだか1つということも変わらない。
--補題：サイズ2以上の同値類からパラレルな頂点をひとつtraceしても、サイズが2以上の同値類が極大なものに限られることも変わらない。
--集合族としては、パラレルな頂点を持つ頂点をtraceしていくことにより、パラレルな頂点を持たない集合族を得ることができる。
--補題： 集合族に対して、パラレルな要素を持つ要素で、rareな頂点をtraceして平均rareであれば、もともと平均rareである。
--この補題は順序とは関係なく、一般に成り立つ。
--この補題の証明は、すでにParallel.leanのファイルの中で完了している。
--補題: 集合族に対して、パラレルな要素を持つものが平均rareであることを示すためには、サイズ2以上の同値類をすべて1頂点にまでtraceしたものが平均rareであることを示せば良い。
--パラレルな頂点の個数に関する帰納法で示すことができる。サイズがkの同値類があれば、k-1を足すということでbase caseが0にするとよい。
--⚪︎半順序と平均rare
--ここまでで、サイズ2以上の同値類はないと仮定してよくなったので、同値類のサイズは全部1で、頂点集合ground上の半順序と思うことができる。
--パラレルな頂点がなくなったあとは、グラフ論の森(forest)で各連結成分に根が指定されているものと思うことができる。根から遠い頂点が下となる。
--パラレルな頂点がなくなったあとは、極大な頂点(=グラフの根)をdeletionしていく。集合族としては、根のdeletionと考えても、traceと考えても同じ。
--補題：半順序集合の順序idealの個数は、台集合の数よりも同じか多い。
--これは、各要素を単項idealに対応させれば、それが単射になることからわかる。反対称律から、単射でなければパラレルな要素が出てくる。
--われわれの枠組みに限らない一般的な定理となる。principal_ideal_injectiveで証明済み。
--⚪︎半順序が連結の場合
--補題：サイズnの台集合の集合族で、半順序が定義されているとする。生成根付き集合のステムサイズは1で、親はたかだか1個で、パラレルな頂点はないとする。半順序の極大頂点は一つとすると、
--極大頂点を通るhyperedgeは、たかだか1つである。
--証明は、順序idealの定義から自明。極大な頂点が生成する単項idealがひとつ増えることになる。
--補題：極大な頂点を集合族からdeletionしても、その頂点と関係ない部分の半順序関係は変わらない。よって、各頂点に関して、親はひとつであるような半順序がそのままのこる。
--補題：上のセッティングで、極大な要素をdeletionした極大n-1の大きさの台集合を持つ集合族が平均rareであれば、もとの集合族も平均rareである。
--証明
--極大な頂点をdeletionすることでサイズn-1の集合族が得られる。極大な頂点を付け加えることで、元の順序idealに加えて、順序idealがちょうどひとつ付け加わる。
--証明は、付け加わった順序idealの大きさをkとすると、kはn以下で、頂点を付け加わることで、
--順序idealの大きさの和はkだけ増える。
--順序idealの個数は、ちょうど1増える。
--台集合の大きさは1増える。
--よって、(順序idealの大きさの和*2-順序idealの個数*台集合の大きさ)は増えることはない。
--sumを順序idealのもともとの和として、numを順序idealのもともとの個数として、num >= nであり、k <= nであるので、
--増加分は、((sum+k)*2 - (n+1)(num+1))-(2*sum - n*num) = 2k-n-num-1 <= 0である。
--証明終わり
--⚪︎半順序が連結でない場合
--まずは連結成分が2個の場合を考える。もしくは、頂点集合を2分割して、それぞれの間の頂点には大小関係がない場合を考える。
--片方の順序idealの大きさの和をs1、順序idealの個数をh1、頂点集合の大きさをn1とする。
--もう片方の順序idealの大きさの和をs2、順序idealの個数をh2、頂点集合の大きさをn2とする。
--合わせた半順序集合に関して順序idealの大きさの和は、s1*h2+s2*h1である。
--合わせた半順序集合の順序idealの個数は、h1*h2である。
--合わせた半順序集合の台集合の大きさは、n1+n2である。
--平均rareであるためには、(s1*h2+s2*h1)*2-(h1*h2)*(n1+n2)<=0である。
--それぞれが平均rareなので、s1*2-h1*n1<=0, s2*2-h2*n2<=0であることからこれはいえる。
--連結成分が3個以上の場合は、帰納法で証明することになる。

--このfunctionalgraphのファイルは、Setupを使う前なので、古いファイルとして、importされない方向か。

--Preorderを定義する前にClosureSystemを定義してしまったが、Preorderを導入してからそれのidealとして導入した方が良かったかも。
/-
def family_onestem_eachvertex (V: Finset α) (f : α → α) (nonemp:V.Nonempty): ClosureSystem α :=
{
  ground := V,
  sets := fun s : Finset α => s ⊆ V ∧ (∀ v ∈ V, f v ∈ s → v ∈ s)
  inc_ground:= by
    intro s a
    exact a.1
  nonempty_ground := by
    exact nonemp
  has_ground := by
    simp_all only
    constructor
    · simp_all only [subset_refl]
    · intro v a a_1
      simp_all only
  intersection_closed := by
    intro s t a b
    simp_all only
    constructor
    ·
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right_1⟩ := b
      intro v hv
      simp_all only [Finset.mem_inter]
      obtain ⟨left_2, right_2⟩ := hv
      apply left_1
      simp_all only
    ·
      intro v a_1 a_2
      simp_all only [Finset.mem_inter, and_self]

  }

--関数fからRootedSetsを導入してみた。これは、直接Closureを定義できるし、このアプローチのほうがいいかも。f:V ->Vのほうがよい。
noncomputable def rootedset_onestem_eachvertex {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : α → α) (valid:∀ v : { x : α // x ∈ V }, f v.val ∈ V \ {v.val}) (nonemp:Finset.Nonempty V): RootedSets α :=
{
  ground := V,
  rootedsets := V.attach.image (λ v => ValidPair.mk ({f v.val}) v.val (by
     let vl := valid v
     rw [@mem_sdiff] at vl
     rw [@not_mem_singleton] at vl
     exact not_mem_singleton.mpr (id (Ne.symm vl.right))))
  inc_ground := by
    intros p hp
    specialize hp
    constructor
    · simp at hp
      obtain ⟨v, ⟨hv, ⟨hv_in, hp_in⟩⟩⟩ := hp
      simp
      simp_all only [mem_sdiff, Finset.mem_singleton, Subtype.forall]
    ·
      simp_all only [Finset.mem_image, mem_attach, true_and, Subtype.exists]
      obtain ⟨w, h⟩ := hp
      obtain ⟨w_1, h⟩ := h
      subst h
      simp_all only
  nonempty_ground := by
     exact nonemp,
}

--fの定義をV -> Vにしたので、validの条件が変わった。これは、f v ≠ vという条件になった。でもRootedSets alphaのほうが好ましい？
noncomputable def rootedset_onestem_eachvertex_sub {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:Finset.Nonempty V): RootedSets V :=
{
  ground := V.attach,
  rootedsets := V.attach.image (λ v => ValidPair.mk ({(f v)}:Finset V) v (by
     let vl := valid v
     simp_all only [Finset.mem_singleton, ne_eq]
     obtain ⟨val, property⟩ := v
     apply Aesop.BuiltinRules.not_intro
     intro a
     exact valid ⟨val, property⟩ a.symm
      ))
  inc_ground := by
    intros p hp
    specialize hp
    constructor
    · simp at hp
      obtain ⟨v, ⟨hv, ⟨hv_in, hp_in⟩⟩⟩ := hp
      simp
    ·
      simp_all only [Finset.mem_image, mem_attach, true_and, Subtype.exists]
  nonempty_ground := by
    simp_all only [ne_eq, Subtype.forall, attach_nonempty_iff]
  }

--この形が一番良いか？alpha上のRootedSetsを与える。
noncomputable def rootedset_onestem_eachvertex_V {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:Finset.Nonempty V): RootedSets α :=
{
  ground := V,
  rootedsets :=
  V.attach.image (λ v => ValidPair.mk ({(f v).val}:Finset α) v (by
    have : v ∉ ({f v}:Finset V) := by
      simp_all only [ne_eq, Subtype.forall, Finset.mem_singleton]
      obtain ⟨val, property⟩ := v
      apply Aesop.BuiltinRules.not_intro
      intro a
      exact valid _ _ a.symm
    simp
    by_contra h_contra
    --cases h_contraこれを入れるとbyでエラー
    simp_all only [Finset.mem_singleton, ne_eq]
    have h_eq : v = f v := by
      apply Subtype.eq
      exact h_contra
    contradiction
  ))

  inc_ground := by
    intros p hp
    specialize hp
    constructor
    · simp at hp
      obtain ⟨v, ⟨hv, ⟨hv_in, hp_in⟩⟩⟩ := hp
      simp
    ·
      simp_all only [Finset.mem_image, mem_attach, true_and, Subtype.exists]
      obtain ⟨w, h⟩ := hp
      obtain ⟨w_1, h⟩ := h
      subst h
      simp_all only

  nonempty_ground := by
    simp_all only [ne_eq, Subtype.forall, attach_nonempty_iff]
  }

--preorderになるというlemmaの形ではうまくいかなかったので、instanceにしてみる。Preorderがサブタイプに定義されている。alphaには定義されてないので注意。
--noncomputable instance size_one_preorder {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : α → α) (valid:∀ v : { x : α // x ∈ V }, f v.val ∈ V \ {v.val}) (nonemp:V.Nonempty):
--  Preorder { x // x ∈ V } := size_one_circuits_preorder (rootedset_onestem_eachvertex V f valid nonemp)

noncomputable instance size_one_preorder {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty):
  Preorder { x // x ∈ V } := size_one_circuits_preorder (rootedset_onestem_eachvertex_V V f valid nonemp)

theorem functional_family_average_rare (V: Finset α) (f : α → α) (nonemp:V.Nonempty) :
  (family_onestem_eachvertex V f nonemp).toSetFamily.normalized_degree_sum ≤ 0 :=
by
  sorry

--前順序が同値類を作り、それ上の半順序を作るという一般的な話の部分。setoidが導入されている。
def equiv_rel {α : Type} [Preorder α] (x y : α) : Prop := x ≤ y ∧ y ≤ x

lemma equiv_rel_refl {α : Type} [Preorder α]  : Reflexive (@equiv_rel α _) := fun x => ⟨le_refl x, le_refl x⟩

lemma equiv_rel_symm  {α : Type} [Preorder α] : Symmetric (@equiv_rel α _) :=
  fun (x y : α) (h : equiv_rel x y) => ⟨h.2, h.1⟩

lemma equiv_rel_trans {α : Type} [Preorder α] : Transitive (@equiv_rel α _) :=
  fun x y z ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨le_trans h1 h3, le_trans h4 h2⟩

lemma equiv_rel_equiv {α : Type}  [Preorder α]: Equivalence (@equiv_rel α _) :=
  ⟨equiv_rel_refl, @equiv_rel_symm α _, @equiv_rel_trans α _⟩

instance setoid_preorder {α : Type}[Preorder α]: Setoid α := ⟨@equiv_rel α _, equiv_rel_equiv⟩

--消すとエラー。[∀ a b : α, Decidable (a ≤ b)]も必要。
noncomputable instance decidableEq_Quotient_setoid_preorder {α : Type} [Preorder α] [∀ a b : α, Decidable (a ≤ b)] :
  DecidableEq (Quotient (setoid_preorder : Setoid α)) :=
by
  infer_instance

--noncomputable instance preorder_Quotient_setoid_preorder {α : Type} [Preorder α] : Preorder (Quotient (setoid_preorder : Setoid α)) :=

noncomputable instance finite_quotient_classes {α : Type} [Preorder α] [Fintype α]: Finset (Quotient (@setoid_preorder α _)) :=
  Finset.image (@Quotient.mk α setoid_preorder) (Finset.univ:Finset α)




example [Preorder α]: Nonempty (Finset (Quotient (@setoid_preorder α _))) :=
  ⟨finite_quotient_classes⟩

instance quotient_partial_order {α : Type}[Preorder α]: PartialOrder (Quotient (@setoid_preorder α _)) where
  le := Quotient.lift₂ (fun x y => x ≤ y) (fun a b c d ⟨hab1, hab2⟩ ⟨hcd1, hcd2⟩ =>
    propext ⟨fun h => le_trans hab2 (le_trans h hcd1),
    by
      intro a_1
      --hab1 : a ≤ cと、a_1 : c ≤ dと、hcd2 : d ≤ bからa ≤ bがいえる。
      exact le_implies_le_of_le_of_le hab1 hcd2 a_1
    ⟩)
  le_refl := fun x => Quotient.inductionOn x (fun a => le_refl a)
  le_trans := fun x y z => Quotient.inductionOn₃ x y z (fun a b c => le_trans)
  le_antisymm := fun x y => Quotient.inductionOn₂ x y (fun a b h1 h2 => Quotient.sound ⟨h1, h2⟩)

--前順序の大小をsetoid上の半順序に持ち上げ。
lemma quotient_le_iff {α : Type}[Preorder α] (a b : α) :
  (quotient_partial_order.le (Quotient.mk setoid_preorder a : Quotient (@setoid_preorder α _))  (Quotient.mk setoid_preorder b)) ↔ a ≤ b := by
  rfl  -- quotient_partial_order での定義を見ると、ちょうどこの形になります

--前順序の要素を対応する同値類に移す。
noncomputable def pullback {α : Type} [Fintype α] [Preorder α]
  (J : Finset (Quotient (@setoid_preorder α _))) : Finset α :=
  { a : α | Quotient.mk setoid_preorder a ∈ J }

def isMaximal [Preorder α] (a : α) : Prop :=
  ∀ b : α, a ≤ b → b ≤ a

/--
商集合上 `(Quotient setoid_preorder, ≤)` における「極大元」であることを表す述語です。
-/
def isMaximalQ [Preorder α](x : Quotient (@setoid_preorder α _)) : Prop :=
  ∀ y, x ≤ y → y ≤ x

/-
「元の前順序で `a` が極大元である」ことと、
「商集合上で `Quotient.mk a` が極大元である」ことは同値である、という主張を証明します。
-/

omit [Fintype α] in
omit [DecidableEq α] in
lemma isMaximal_iff [Preorder α] (a : α) :
  isMaximal a ↔ isMaximalQ (Quotient.mk setoid_preorder a) := by
  constructor
  · --------------------
    -- (→) 方向の証明
    intro ha  -- `ha` : a は元の前順序で極大
    intro x hx
    -- x は商集合上の元なので、代表元 b を取り出す
    rcases Quotient.exists_rep x with ⟨b, rfl⟩
    -- hx : Quotient.mk a ≤ Quotient.mk b から a ≤ b を得る
    rw [quotient_le_iff] at hx
    -- a が極大なので b ≤ a になる
    have hba := ha b hx
    -- すると商集合上も Quotient.mk b ≤ Quotient.mk a が成り立つ
    rw [quotient_le_iff]
    exact hba
  · --------------------
    -- (←) 方向の証明
    intro ha  -- `ha` : 商集合で Quotient.mk a が極大
    intro b hab
    -- a ≤ b から商集合でも Quotient.mk a ≤ Quotient.mk b となる
    have h : (Quotient.mk setoid_preorder a : Quotient setoid_preorder) ≤ Quotient.mk setoid_preorder b := by
      rw [quotient_le_iff]
      exact hab
    -- 商集合での極大性から Quotient.mk b ≤ Quotient.mk a
    specialize ha (Quotient.mk setoid_preorder b) h
    -- これを a, b 間の関係に戻す
    rw [quotient_le_iff] at ha
    exact ha

/--
「元の前順序での極大元の集合」-
「商集合上での極大元の集合」とが、商写像 `Quotient.mk` を通じて
ちょうど同じものになる、ということを集合レベルでも示せます。
-/
noncomputable def MaxSet  [Preorder α][Fintype α]:= ({ a : α | isMaximal a }:Finset α)
noncomputable def MaxQuotSet {α : Type} [Preorder α] [Fintype α] : Finset (Quotient (@setoid_preorder α _)) :=
  { x : Quotient (@setoid_preorder α _) | isMaximalQ x }

omit [Fintype α] [DecidableEq α] in
lemma MaxQuotSet_eq_image [Preorder α] [Fintype α]:
  MaxQuotSet = Finset.image (Quotient.mk (@setoid_preorder α _)) MaxSet := by
  ext x
  constructor
  · --------------------
    -- (→) x が商集合で極大ならば、その代表元 a も元の前順序で極大
    intro hx
    rcases Quotient.exists_rep x with ⟨a, rfl⟩
    rw [Finset.mem_image]
    use a
    constructor
    · -- a が元の前順序で極大であることは、isMaximal_iff の逆向きで分かる
      dsimp [MaxQuotSet] at hx
      rw [Finset.mem_filter] at hx
      dsimp [MaxSet]
      rw [mem_filter]
      simp_all only [Finset.mem_univ, true_and]
      rw [isMaximal_iff]
      simp_all only
    · rfl  -- x = Quotient.mk a
  · --------------------
    -- (←) x が Quotient.mk a で、a が元の前順序で極大なら、x も商集合上で極大
    intro hx
    dsimp [MaxQuotSet]
    rw [Finset.mem_image] at hx
    rw [Finset.mem_filter]
    constructor
    · simp_all only [Finset.mem_univ]
    · dsimp [isMaximalQ]
      intro y hy
      rcases Quotient.exists_rep y with ⟨b, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hx
      dsimp [MaxSet] at ha
      rw [Finset.mem_filter] at ha
      simp_all only [Finset.mem_univ, true_and]
      apply ha
      exact hy

structure IsIdeal {α : Type} [Fintype α] [Preorder α] (I : Finset α) : Prop where
  down_closed :
    ∀ {x}, x ∈ I → ∀ {y}, y ≤ x → y ∈ I
  directed :
    ∀ {x y}, x ∈ I → y ∈ I → ∃ z ∈ I, x ≤ z ∧ y ≤ z

/--
商集合 `(Quotient setoid_preorder, ≤)` における順序イデアル。
-/
structure IsIdealQ {α : Type} [Fintype α] [Preorder α]
  (J : Finset (Quotient (@setoid_preorder α _))) : Prop where
  down_closed :
    ∀ {x}, x ∈ J → ∀ {y}, y ≤ x → y ∈ J
  directed :
    ∀ {x y}, x ∈ J → y ∈ J → ∃ z ∈ J, x ≤ z ∧ y ≤ z

--Preorderのidealと、setoid上のidealの同値性を示す。
lemma IsIdealQ.pullback_isIdeal {α : Type} [Fintype α][Preorder α]
    {J : Finset (Quotient (@setoid_preorder α _))}
    (hJ : IsIdealQ J) :
    IsIdeal (pullback J) := by
  constructor
  · -- 下に閉じていることを示す
    -- x ∈ pullback J かつ y ≤ x のとき y ∈ pullback J を示す
    intro x hx y hyx
    -- hx: Quotient.mk x ∈ J, ここから下に閉じている性質を使う
    -- まず y ≤ x から (Quotient.mk y) ≤ (Quotient.mk x)
    have : (Quotient.mk setoid_preorder y : Quotient _) ≤ Quotient.mk setoid_preorder x := by
      rw [quotient_le_iff]
      exact hyx
    -- hJ.down_closed で J が商集合上で下に閉じているので
    -- Quotient.mk y も J に入る
    dsimp [pullback]
    simp
    have hhx: ⟦x⟧ ∈ J :=
    by
      dsimp [pullback] at hx
      simp_all only [mem_filter, Finset.mem_univ, true_and]
    exact hJ.down_closed hhx this
  · -- 有向性を示す
    intro x y hx hy
    -- x, y ∈ pullback J すなわち Quotient.mk x, Quotient.mk y が J に属する
    have hhx:  ⟦x⟧ ∈ J := by
      dsimp [pullback] at hx
      simp_all only [mem_filter, Finset.mem_univ, true_and]
    have hhy : ⟦y⟧ ∈ J := by
      dsimp [pullback] at hy
      simp_all only [mem_filter, Finset.mem_univ, true_and]
    obtain ⟨z, hzJ, hxz, hyz⟩ :=
      hJ.directed hhx hhy
    -- すると z ∈ J の代表元を w として、Quotient.mk w = z とすると w ∈ pullback J となる
    -- z はすでに (Quotient (@setoid_preorder α _)) 型の要素なので、代表元を取り出す
    rcases Quotient.exists_rep z with ⟨w, rfl⟩
    -- hxz : Quotient.mk x ≤ Quotient.mk w から x ≤ w へ
    rw [quotient_le_iff] at hxz hyz
    -- あとは w が pullback J に属することを示せば完了
    use w
    constructor
    · -- w ∈ pullback J を示す
      dsimp [pullback]
      simp
      exact hzJ
    · exact ⟨hxz, hyz⟩

noncomputable def pushforward {α : Type} [Fintype α] [Preorder α]
  (I : Finset α) : Finset (Quotient (@setoid_preorder α _)) :=
  Finset.univ.filter (fun q => ∃ a ∈ I, Quotient.mk setoid_preorder a = q)

/--
元の前順序でのイデアル I は、その同値類の集まり（pushforward I）も
商集合上のイデアルを成す。
-/
lemma IsIdeal.pushforward_isIdealQ {α : Type} [Fintype α] [Preorder α]
    {I : Finset α} (hI : IsIdeal I) :
    IsIdealQ (pushforward I) := by
  constructor
  · -- 下に閉じている
    intro x hx y hyx
    dsimp [pushforward] at hx
    rw [Finset.mem_filter] at hx
    rcases hx.2 with ⟨a, haI, rfl⟩
    rcases Quotient.exists_rep y with ⟨b, rfl⟩
    rw [quotient_le_iff] at hyx  -- b ≤ a
    -- I が下に閉じているので a ∈ I, b ≤ a ⇒ b ∈ I
    have hbI := hI.down_closed haI hyx
    dsimp [pushforward]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ (⟦b⟧), ⟨b, hbI, rfl⟩⟩
  · -- 有向性
    intro x y hx hy
    dsimp [pushforward] at hx hy
    rw [Finset.mem_filter] at hx hy
    rcases hx.2 with ⟨a, haI, rfl⟩
    rcases hy.2 with ⟨b, hbI, rfl⟩
    -- I が有向 ⇒ ∃ c ∈ I, a ≤ c ∧ b ≤ c
    rcases hI.directed haI hbI with ⟨c, hcI, hac, hbc⟩
    use Quotient.mk setoid_preorder c
    constructor
    · dsimp [pushforward]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨c, hcI, rfl⟩⟩
    · rw [quotient_le_iff]
      rw [quotient_le_iff]
      exact ⟨hac, hbc⟩
section
variable --つかってないかも。
  {α : Type} [Fintype α] [DecidableEq α]
  (V : Finset α)
  (f : V → V)
  (valid : ∀ v : V, f v ≠ v)
  (nonemp : V.Nonempty)

--つかってないというかうまくいかなかった。
noncomputable instance local_size_one_preorder :
    Preorder { x // x ∈ V } :=
  size_one_preorder V f valid nonemp

def localCovBy (myLT : X → X → Prop) (a b : X) : Prop :=
  myLT a b ∧ ∀ c, myLT a c → myLT c b → False


-/
