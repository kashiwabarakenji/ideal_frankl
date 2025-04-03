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

----------------------
--setupの定義に必要な部分。
-----------------------

--この形が一番良いか？alpha上のRootedSetsを与える。集合族を定義するのにこの形を利用している。
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

--setupを定義する時に利用している。
noncomputable def size_one_preorder {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty):
  Preorder { x // x ∈ V } := size_one_circuits_preorder (rootedset_onestem_eachvertex_V V f valid nonemp)


--前順序が同値類を作り、それ上の半順序を作るという一般的な話の部分。setoidが導入されている。
def equiv_rel {α : Type} [Preorder α] (x y : α) : Prop := x ≤ y ∧ y ≤ x

lemma equiv_rel_refl {α : Type} [Preorder α]  : Reflexive (@equiv_rel α _) := fun x => ⟨le_refl x, le_refl x⟩

lemma equiv_rel_symm  {α : Type} [Preorder α] : Symmetric (@equiv_rel α _) :=
  fun (x y : α) (h : equiv_rel x y) => ⟨h.2, h.1⟩

lemma equiv_rel_trans {α : Type} [Preorder α] : Transitive (@equiv_rel α _) :=
  fun _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨le_trans h1 h3, le_trans h4 h2⟩

lemma equiv_rel_equiv {α : Type}  [Preorder α]: Equivalence (@equiv_rel α _) :=
  ⟨equiv_rel_refl, @equiv_rel_symm α _, @equiv_rel_trans α _⟩

--preorderから定義するsetoidのインスタンス。setupの定義で用いる。instanceでなくて、defのほうがいいのかも。
def setoid_preorder {α : Type}[Preorder α]: Setoid α := ⟨@equiv_rel α _, equiv_rel_equiv⟩

structure Setup (α : Type) [Fintype α] [DecidableEq α] where
  (V        : Finset α)
  (nonemp   : V.Nonempty)
  (f        : V → V)
  (valid    : ∀ v : V, f v ≠ v)
  (pre      : Preorder {x // x ∈ V})
  (h_pre    : pre = size_one_preorder V f valid nonemp)
  (setoid   : Setoid {x // x ∈ V})
  (h_setoid : setoid = setoid_preorder) --これは順序ではなく、同値類まで。

instance (s : Setup α) : Preorder {x // x ∈ s.V} := s.pre

----------------------
--setupの定義からClosure Systemを導入する部分。
-----------------------

--setupからrootedsetを作るもの。fから作るには、rootedset_onestem_eachvertex_Vを利用すれば良い。setupに含めてもよいかも。
--RootedSetsから2項関係にするには、R_from_RS1 を用いると、ステムサイズ1のものだけから2項関係を作ってくれる。
noncomputable def rootedset_from_setup {α : Type} [Fintype α] [DecidableEq α] (s: Setup α) : RootedSets α :=
 rootedset_onestem_eachvertex_V s.V s.f s.valid s.nonemp

--setupを与える形で書き直した。
noncomputable def preorder_ideal_system (s:Setup α): ClosureSystem α :=
{
  ground := s.V
  sets := fun ss : Finset α => ss ⊆ s.V ∧(∀ v : s.V, v.val ∈ ss → (∀ w : s.V, s.pre.le w v → w.val ∈ ss)),
  inc_ground:= by
    intro ss a
    exact a.1
  nonempty_ground := by
    exact s.nonemp
  has_ground := by
    simp_all only
    constructor
    · simp_all only [subset_refl]
    ·
      intro v a a_1
      intro a_2
      simp_all only [coe_mem]
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
      simp_all only [Subtype.forall]
      apply left_1
      simp_all only
    ·
      intro v a_1 w a_2
      simp_all only [Subtype.forall, Finset.mem_inter]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := w
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right_1⟩ := b
      obtain ⟨left_2, right_2⟩ := a_1
      simp_all only
      apply And.intro
      · tauto
      · tauto
}

-------------
--同値類の関係。

--Setupを使ってないものは今後は推奨しないかも。。使ってないかもしれない。
--noncomputable def eqClass_subtype {α : Type} [DecidableEq α] (V : Finset α) [Setoid {x : α // x ∈ V}] (x : {x : α // x ∈ V}) : Finset {x // x ∈ V} :=
--  V.attach.filter (fun y => Setoid.r x y)

--下で使っている。
noncomputable def eqClass_setup (s: Setup α) (x : {x : α // x ∈ s.V}) : Finset {x // x ∈ s.V} :=
  s.V.attach.filter (fun y => s.setoid.r x y)

--同じ同値類に入っている要素には大小関係がある。
lemma eqClass_le (s: Setup α) : (x y: {x : α // x ∈ s.V}) → y ∈ eqClass_setup s x → s.pre.le x y :=
by
  intro x y h
  simp [eqClass_setup] at h
  rw [s.h_setoid] at h
  simp_all only [AntisymmRel.setoid_r]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  exact h.1

lemma eqClass_ge (s: Setup α) : (x y: {x : α // x ∈ s.V}) → y ∈ eqClass_setup s x → s.pre.le y x :=
by
  intro x y h
  simp [eqClass_setup] at h
  rw [s.h_setoid] at h
  simp_all only [AntisymmRel.setoid_r]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  exact h.2

lemma eqClass_eq (s: Setup α) : (x y: {x : α // x ∈ s.V}) → s.pre.le x y →s.pre.le y x → eqClass_setup s x = eqClass_setup s y :=
by
  intro x y hxy hyx
  ext z
  apply Iff.intro
  ·
    simp [eqClass_setup]
    rw [s.h_setoid]
    simp_all only [AntisymmRel.setoid_r]
    obtain ⟨xval, xproperty⟩ := x
    obtain ⟨yval, yproperty⟩ := y
    dsimp [AntisymmRel]
    intro h
    constructor
    ·
      exact s.pre.le_trans ⟨yval, yproperty⟩ ⟨xval, xproperty⟩ z hyx h.1
    ·
      exact s.pre.le_trans z ⟨xval, xproperty⟩ ⟨yval, yproperty⟩ h.2 hxy
  ·
    simp [eqClass_setup]
    rw [s.h_setoid]
    simp_all only [AntisymmRel.setoid_r]
    obtain ⟨xval, xproperty⟩ := x
    obtain ⟨yval, yproperty⟩ := y
    dsimp [AntisymmRel]
    intro h
    constructor
    ·
      exact s.pre.le_trans ⟨xval, xproperty⟩ ⟨yval, yproperty⟩ z hxy h.1
    ·
      exact s.pre.le_trans z ⟨yval, yproperty⟩ ⟨xval, xproperty⟩ h.2 hyx

--必要に迫られて作った。
lemma eqClass_eq_rev (s: Setup α) : (x y z: {x : α // x ∈ s.V}) → x ∈ eqClass_setup s z → y ∈ eqClass_setup s z → s.pre.le x y ∧ s.pre.le y x:=
by
  intro x y z hx hy
  constructor
  · dsimp [eqClass_setup] at hx
    dsimp [eqClass_setup] at hy
    rw [s.h_setoid] at hx hy
    simp_all only [AntisymmRel.setoid_r]
    obtain ⟨xval, xproperty⟩ := x
    obtain ⟨yval, yproperty⟩ := y
    simp_all only [mem_filter, mem_attach, true_and]
    obtain ⟨val, property⟩ := z
    rw [AntisymmRel] at hx hy
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hy
    exact right.trans left_1
  · dsimp [eqClass_setup] at hx
    dsimp [eqClass_setup] at hy
    rw [s.h_setoid] at hx hy
    simp_all only [AntisymmRel.setoid_r]
    obtain ⟨xval, xproperty⟩ := x
    obtain ⟨yval, yproperty⟩ := y
    simp_all only [mem_filter, mem_attach, true_and]
    obtain ⟨val, property⟩ := z
    rw [AntisymmRel] at hx hy
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hy
    apply Preorder.le_trans
    assumption
    simp_all only

-------------------------------
---以下は、古いというか、初期のもの。

--Preorderを定義する前にClosureSystemを定義してしまったが、Preorderを導入してからそれのidealとして導入した方が良かったかも。
--現状使っていない。
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
