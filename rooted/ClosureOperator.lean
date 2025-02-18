--Closure Operatorの基本的な定義と補題。
--閉集合族からClosure Operatorが定義できること。Closure Operatorから閉集合が定義できることが証明されている。
--閉包作用素は、無限集合に対しても定義できるが、ここでは有限集合上で考えている。
import LeanCopilot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import rooted.CommonDefinition

--set_option maxHeartbeats 1000000

variable {α : Type}  [DecidableEq α] [Fintype α]

--定義に集合族は必要なく、　台集合さえわかればいい。でも台集合を利用するので、SetFamilyを引数にとっている。
structure SetFamily.preclosure_operator (ground:Finset α) where
  (cl : Finset ground → Finset ground)
  (extensive : ∀ s : Finset ground, s ⊆ cl s)
  (monotone : ∀ s t : Finset ground, s ⊆ t → cl s ⊆ cl t)

--一般的なclosure operatorの定義。
structure SetFamily.closure_operator (ground:Finset α) extends SetFamily.preclosure_operator ground where
  (idempotent : ∀ s : Finset ground, cl s = cl (cl s))

def finsetIntersection {α : Type} [DecidableEq α]
  (family : Finset (Finset α)) : Finset α :=
  (family.sup id).filter (fun x => ∀ f ∈ family, x ∈ f)

--閉集合族から定義されたclosure operatorの定義。
--これで閉包作用素の値は定義できるが、この段階では閉包作用素の定義を満たしているかはわからなない。closure_operator_from_SFで証明される。
--閉包関数は、subtypeに対してていぎされていることに注意。
def closureOperator {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets] (s : Finset F.ground) : Finset F.ground :=
  let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
  let ios := finsetIntersection (F.ground.powerset.filter (fun (t : Finset α) => F.sets t ∧ sval ⊆ t))
  ios.subtype (λ x => x ∈ F.ground)

--閉集合族から定義された作用素がextensiveを満たすこと。
--closure systemでないと全体集合が含まれないので、ただの集合族では証明できない。
lemma extensive_from_SF_finset {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)[DecidablePred F.sets]:
  ∀ s : Finset F.ground, s ⊆ closureOperator F s :=
by
  dsimp [closureOperator]
  intro s
  dsimp [finsetIntersection]
  simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp]
  rw [Finset.map_eq_image]
  simp
  intro x hx
  rw [@Finset.mem_subtype]
  rw [Finset.mem_filter]
  simp
  constructor

  · obtain ⟨val, property⟩ := x
    simp_all only
    use F.ground
    simp_all only [subset_refl, and_true]--
    apply And.intro
    · simp_all only
    · apply And.intro
      · exact F.has_ground
      · simp [Finset.image_subset_iff]

  · intro f a a_1 a_2
    obtain ⟨val, property⟩ := x
    simp_all only
    apply a_2
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]--

--集合族から定義された作用素がmonotoneを満たすこと。名前は変えた方がいいかも。
lemma monotone_from_SF_finset {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)[DecidablePred F.sets]:
  ∀ s t : Finset F.ground, s ⊆ t → closureOperator F s ⊆ closureOperator F t :=
by
  dsimp [closureOperator]
  intro s t h
  dsimp [finsetIntersection]
  simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp]
  rw [Finset.map_eq_image]
  simp
  intro x hx
  rw [@Finset.mem_subtype]
  rw [Finset.mem_filter]
  simp
  constructor
  · use F.ground
    simp_all only [subset_refl]
    apply And.intro
    · constructor
      · simp_all only [Finset.mem_filter, Finset.mem_sup, Finset.mem_powerset, id_eq]
      · constructor
        · exact F.has_ground
        · simp_all only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_sup]--
          obtain ⟨val, property⟩ := x

          intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,exists_eq_right]--
          obtain ⟨w_1, h_1⟩ := hx
          simp_all only [subset_refl]

    · simp_all only [Finset.coe_mem]

  · intro f a a_1 a_2
    obtain ⟨val, property⟩ := x
    simp_all only [Finset.mem_subtype, Finset.mem_filter, Finset.mem_sup, Finset.mem_powerset, id_eq]--
    obtain ⟨left, right⟩ := hx
    obtain ⟨w, h_1⟩ := left
    obtain ⟨left, right_1⟩ := h_1
    simp_all only [subset_refl]
    apply right
    · simp_all only [subset_refl]
    · simp_all only [subset_refl]
    · intro x hx
      simp_all only [subset_refl, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w_1, h_1⟩ := hx
      apply a_2
      simp_all only [subset_refl, Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right,
        exists_eq_right, exists_true_left]
      exact h h_1

--2つ以上の閉集合の共通部分がまた閉集合であること。
lemma finite_intersection_in_closureSystem
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)
  (M : Finset (Finset α))
  (M_nonempty : M.Nonempty)
  (all_inF : ∀ T ∈ M, F.sets T)
  : F.sets (finsetIntersection M) := by
  classical

  -- **ここで `Finset.induction_on` を使う**
  induction M using Finset.induction_on --(p := λ (s : Finset (Finset α))=> F.sets (finsetIntersection s))
    -- 1) base case: s = ∅
  case empty =>
    -- finsetIntersection ∅ = F.ground なので F.sets (finsetIntersection ∅)
    dsimp [finsetIntersection]
    simp
    simp_all only [Finset.not_nonempty_empty]

    -- 2) induction step: s = insert T₀ M' と仮定
  case insert T₀ M' T₀_not_in_M' ih =>
    cases M'.eq_empty_or_nonempty with
    | inl hM'_empty =>
      -- M' = ∅ の場合 => M = {T₀}
      -- finsetIntersection {T₀} = T₀
      have : finsetIntersection {T₀} = T₀ := by
        apply Finset.ext
        intro x
        simp only [finsetIntersection, Finset.mem_filter, Finset.sup_singleton,
                    Finset.mem_singleton, id_eq, and_assoc]
        -- 「x ∈ T₀ ∧ ∀ f ∈ {T₀}, x ∈ f」は x ∈ T₀ と同値
        subst hM'_empty
        simp_all only [Finset.not_mem_empty, not_false_eq_true, forall_eq, and_self]
      subst hM'_empty
      simp_all only [insert_emptyc_eq,Finset.mem_singleton]--

    | inr hM'_nonempty =>
      -- M' が非空 => 帰納仮定 ih : F.sets (finsetIntersection M')
      -- T₀ も F.sets (all_inF が保証) => 交わりに閉じている => T₀ ∩ finsetIntersection M' ∈ F.sets
      have T₀_inF    := all_inF T₀ (Finset.mem_insert_self T₀ M')
      have M'_inFset := ih  -- これが帰納仮定 (insert の引数 ih)
      -- finsetIntersection (insert T₀ M') = T₀ ∩ finsetIntersection M'
      have key : finsetIntersection (insert T₀ M')
              = T₀ ∩ (finsetIntersection M') := by
        apply Finset.ext
        intro x --xは全体の共通部分から取ってくる。
        simp only [finsetIntersection, Finset.mem_filter,
                    Finset.mem_insert, Finset.mem_inter,
                    Finset.mem_sup, id_eq]
        constructor
        · -- → 方向
          intro h
          -- h : x ∈ (insert T₀ M').sup id ∧ (∀ A ∈ insert T₀ M', x ∈ A)
          --     すなわち (x ∈ T₀ ∪ M'.sup id) ∧ ...
          constructor -- x ∈ T₀ ∩ finsetIntersection M'
          · --x ∈ T₀を示す。
            simp_all only [Finset.mem_insert, or_true, implies_true, imp_self, Finset.insert_nonempty, forall_eq_or_imp,
              true_and, forall_const, exists_eq_or_imp]
          · --(∃ i ∈ M', x ∈ i) ∧ ∀ f ∈ M', x ∈ f
            obtain ⟨left, right⟩ := h
            obtain ⟨w, h⟩ := left
            by_cases h1 : w ∈ M'
            case pos =>
              simp_all only [Finset.mem_insert, or_true, implies_true, imp_self, Finset.insert_nonempty,
                forall_eq_or_imp, true_and, forall_const, and_self, and_true]
              obtain ⟨left, right⟩ := right
              apply Exists.intro
              · apply And.intro
                · exact h1
                · simp_all only
            case neg =>
              have : w = T₀ := by
                simp_all only [Finset.mem_insert,  Finset.insert_nonempty, forall_const, or_false, not_false_eq_true]
              subst this
              simp_all only [Finset.mem_insert, or_true, implies_true, not_false_eq_true,
                Finset.insert_nonempty, forall_eq_or_imp, true_and, or_false, and_true]
              have : Nonempty M' := by
                simp_all only [nonempty_subtype]
                exact hM'_nonempty
              let ww := Classical.choice this
              obtain ⟨val, property⟩ := ww
              apply Exists.intro
              · apply And.intro
                · apply property
                · simp_all only

        · intro a
          simp_all only [implies_true,forall_eq_or_imp,  exists_eq_or_imp, or_self, and_self]--
      convert F.intersection_closed T₀ (finsetIntersection M') T₀_inF (M'_inFset hM'_nonempty (fun T hT => all_inF T (Finset.mem_insert_of_mem hT)))

--閉集合族から定義した閉包作用素の写り先が閉集合になること。
lemma closureOperator_image_in_sets
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets]
  (s : Finset F.ground) :
  F.sets ((closureOperator F s).image Subtype.val) := by

  -- 1. 記号整理
  let sval := s.map ⟨Subtype.val, Subtype.val_injective⟩
  let M := F.ground.powerset.filter (fun t => F.sets t ∧ sval ⊆ t)
  let I := finsetIntersection M  -- "intersection of all t in M"

  -- 2. M が空でないことを示す
  --    理由: ground ∈ M （F.has_ground と sval ⊆ F.ground より）
  have M_nonempty : M.Nonempty := by
    have : F.sets F.ground := F.has_ground
    have : sval ⊆ F.ground := by
      intro x hx
      simp_all only [Finset.mem_map, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_right, exists_eq_right,sval]
      obtain ⟨w, h⟩ := hx
      simp_all only
    simp_all only [sval, M]
    rw [Finset.nonempty_iff_ne_empty]
    simp_all only [ne_eq]
    intro a
    rw [Finset.eq_empty_iff_forall_not_mem] at a
    simp_all only [Finset.mem_filter, Finset.mem_powerset, not_and, subset_refl]

  -- 3. 補題 finite_intersection_in_closureSystem を使って
  --    I = finsetIntersection M が F.sets であることを示す
  have I_inF : F.sets I := by
    apply finite_intersection_in_closureSystem F M
    · exact M_nonempty
    · -- M の要素は (F.sets t ∧ sval ⊆ t) を満たすから、F.sets t
      intro T hT
      exact (Finset.mem_filter.mp hT).2.left

  -- 4. closureOperator F s の map (Subtype.val) がちょうど I に一致する
  have : I = (closureOperator F s).map ⟨Subtype.val, Subtype.val_injective⟩ := by
    -- unfold して確認
    unfold closureOperator
    simp_all only [M, sval, I]
    ext a : 1
    simp_all only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coeFn_mk, Subtype.exists, exists_and_left,exists_prop, exists_eq_right_right, iff_self_and]--
    intro a_1
    rw [finsetIntersection] at a_1
    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_sup, id_eq, subset_refl]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    obtain ⟨left, right_2⟩ := left
    simp_all only [subset_refl]
    apply left
    simp_all only

  -- 5. よって、結論として F.sets ((closureOperator F s).map ... )
  --    は F.sets I と同じなので成立
  simp_all only [M, sval, I]
  convert I_inF
  ext x a : 2
  simp_all only [Finset.mem_image, Subtype.exists, exists_eq_right, Finset.mem_map,Function.Embedding.coeFn_mk]

--finsetIntersectionの基本的な命題。定義を展開するよりも、この補題を使った方が証明が簡単になる。
--familyを明示的な引数に変更。いろいろなところで変更する必要が出てくるかも。
--同様な定理のclosure版は、mem_closure_iff_lemma
lemma mem_finsetIntersection_iff_of_nonempty
  {α : Type} [DecidableEq α]
  (family : Finset (Finset α)) (x : α)
  (hne : family.Nonempty)
  :
  x ∈ finsetIntersection family
  ↔ ∀ f ∈ family, x ∈ f
:= by
  -- unfold して「x ∈ (family.sup id).filter (...)」を展開
  simp only [finsetIntersection, Finset.mem_filter]
  -- x ∈ filter A p ↔ (x ∈ A ∧ p x)
  -- ∴ ここでは「(x ∈ family.sup id) ∧ (∀ f ∈ family, x ∈ f)」
  --
  -- これを「(∀ f ∈ family, x ∈ f)」だけに簡単化するには、
  --   「x が family のすべての要素に入る → x はそのうちの1つ f0 にも入る → よって x ∈ union」
  -- という一方向の補足が必要
  refine Iff.intro
    (fun h => h.2)   -- (←) すでに h.2 が「∀ f ∈ family, x ∈ f」
    (fun hx =>
      -- (→) x が「すべての f ∈ family」に入るならば
      -- union (sup id family) にも入る，かつもちろん (∀f, x∈f)
      have x_in_union : x ∈ family.sup id := by
        -- union に入るためには「ある1つの集合 f ∈ family に x ∈ f」があれば十分
        simp_all only [Finset.mem_sup, id_eq]
        contrapose! hne
        simp_all only [imp_false, Finset.not_nonempty_iff_eq_empty]--
        ext a : 1
        simp_all only [Finset.not_mem_empty]
      -- 以上で (x ∈ sup id ∧ ∀ f∈family, x∈f) が示せる
      ⟨x_in_union, hx⟩
    )

--mem_finsetIntersection_iff_of_nonemptyのclosure版。
--mem_closure_iffだけだとtopological closureの定理と名前がかぶる。
lemma mem_closure_iff_lemma
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets] (s : Finset F.ground) (x : F.ground) :
  x ∈ closureOperator F s ↔ ∀ f :Finset F.ground, s ⊆ f → F.sets (f.image Subtype.val) → x ∈ f :=
by
  -- closureOperator の定義を展開
  simp only [closureOperator]
  -- finsetIntersection の性質を使って「x ∈ closureOperator F s」を展開
  simp
  let family := F.ground.powerset.filter (fun t => F.sets t ∧ s.image Subtype.val ⊆ t)
  have hne: Finset.Nonempty family := by
    use F.ground
    dsimp [family]
    rw [Finset.mem_filter]
    constructor
    · simp_all only [Finset.mem_powerset, subset_refl]
    · constructor
      · exact F.has_ground
      ·
        obtain ⟨val, property⟩ := x
        rw [Finset.image_subset_iff]
        intro x a
        simp_all only [Finset.coe_mem]

  let mfi := @mem_finsetIntersection_iff_of_nonempty _ _ family x hne
  -- あとは、closureOperator の定義に戻す
  dsimp [family] at mfi
  simp at mfi
  simp_all only [family]
  obtain ⟨val, property⟩ := x
  simp_all only
  apply Iff.intro
  · intro a f a_1 a_2
    simp at a
    rw [Finset.map_eq_image] at a
    have : f.image Subtype.val ⊆ F.ground := by
      rw [Finset.image_subset_iff]
      intro x a_3
      simp_all only [Function.Embedding.coeFn_mk, Finset.coe_mem]
    let mfia := mfi.mp a (f.image Subtype.val) this a_2
    have :Finset.image Subtype.val s ⊆ Finset.image Subtype.val f := by
      rw [Finset.image_subset_iff]
      intro x a_3
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
        Finset.coe_mem, exists_const]--
      obtain ⟨val_1, property_1⟩ := x
      exact a_1 a_3
    let miiaf := mfia this
    rw [Finset.mem_image] at miiaf
    simp_all only [Subtype.exists, exists_and_right, exists_eq_right, exists_true_left]

  · intro a
    have : (∀ f ⊆ F.ground, F.sets f → Finset.image Subtype.val s ⊆ f → val ∈ f):=
    by
      intro f a_1 a_2 a_3
      have :s ⊆ (f.subtype (λ x => x ∈ F.ground)) :=
      by
        intro x hx
        simp_all only [Finset.mem_subtype]
        obtain ⟨val_1, property_1⟩ := x
        simp_all only
        apply a_3
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]
      let afs := a (f.subtype (λ x => x ∈ F.ground)) this
      have :F.sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ F.ground) f)) :=
      by
        have : Finset.image Subtype.val (Finset.subtype (fun x => x ∈ F.ground) f) = f:= by
          ext a_4 : 1
          simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
            exists_eq_right_right, and_iff_left_iff_imp]--
          intro a_5
          exact a_1 a_5
        rw [this]
        exact a_2
      let afst := afs this
      dsimp [Finset.subtype] at afst
      simp at afst
      exact afst.1
    let mfia := mfi.mpr this
    rw [Finset.map_eq_image]
    simp_all only [Function.Embedding.coeFn_mk, implies_true]

--閉集合の閉包作用素による像はそのまま。idempotentの証明に利用。
--この命題の逆方向も成り立つ。idempotent_from_SF_finset_lem_mpr
lemma idempotent_from_SF_finset_lem
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets]
  : ∀ s : Finset F.ground, F.sets (s.image Subtype.val) → closureOperator F s = s :=
by
  intro s hFsets
  -- 記号整理：
  -- s : Finset F.ground であり、s.map val は α の Finset
  let sval := s.image (Subtype.val : F.ground → α)

  -- 1. s.map val ∈ M であること (closureOperator の定義で用いた M)
  let M := F.ground.powerset.filter (fun t => F.sets t ∧ sval ⊆ t)
  have s_in_M : sval ∈ M := by
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true, M, sval]
    intro t ht
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    obtain ⟨w, h⟩ := ht
    simp_all only

  -- 2. finsetIntersection M は M のすべての要素に共通する要素の集まり
  let I := finsetIntersection M
  have I_subset_s : I ⊆ sval := by
    -- I は M の要素 t すべてに含まれる要素の集合
    -- かつ s_in_M : sval ∈ M
    -- よって I は sval にも含まれる
    intro x hx
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl,  and_true, Finset.mem_image,
      Subtype.exists, exists_and_right, exists_eq_right, M, sval, I]--
    have : x ∈ F.ground:= by
      simp only [finsetIntersection] at hx
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_sup, id_eq, subset_refl]
      obtain ⟨left, right⟩ := hx
      obtain ⟨w, h⟩ := left
      obtain ⟨left, right_1⟩ := h
      simp_all only [subset_refl]
      apply s_in_M
      simp_all only [subset_refl]

    simp_all only [exists_true_left]
    have : F.ground ∈ Finset.filter (fun t => F.sets t ∧ Finset.image Subtype.val s ⊆ t) F.ground.powerset := by
      simp [Finset.mem_filter, Finset.mem_powerset, F.has_ground]
      simp_all only
    have M_nonempty : M.Nonempty := by
      use F.ground
    let mf := (mem_finsetIntersection_iff_of_nonempty M x M_nonempty).mp hx
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl]
    have : sval ∈ M :=
    by
      simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, M, sval, mf]
    let ms := mf sval this
    simp [sval] at ms
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl,  exists_true_left, M, sval]

  have s_subset_I : sval ⊆ I := by
    -- s.map val は M の各 t に含まれる (by 定義: sval ⊆ t)
    -- よって sval の要素 x は M に属するすべての t でも x ∈ t
    -- ゆえに x ∈ 交わり
    intro x hx
    --simp only [finsetIntersection, Finset.mem_filter]
    -- 「x は M のすべての t に含まれ、かつ x ∈ sup id M」 を示す
    dsimp [I]
    dsimp [finsetIntersection]
    rw [Finset.mem_filter]
    constructor
    · -- x ∈ (M.sup id)
      -- これは「何らかの t ∈ M に x ∈ t」がいえればOK
      -- 実際には t = sval がそう
      apply Finset.mem_sup.mpr
      refine ⟨sval, s_in_M, ?_⟩
      simp only [id_eq]
      exact hx
    · -- x はすべての t ∈ M で t に属する
      intro t ht
      simp_all only [Finset.mem_filter, Subtype.exists, exists_and_right, exists_eq_right, M, sval, I]
      obtain ⟨left, right⟩ := ht
      obtain ⟨left_1, right⟩ := right
      apply right
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]

  -- 以上 2つの包含より I = s.map val
  have : I = sval := by
    apply Finset.Subset.antisymm
    · exact I_subset_s
    · exact s_subset_I

  -- 3. closureOperator F s は I を Finset F.ground に戻したもの
  apply Finset.ext
  intro x
  constructor
  · -- (→) x ∈ closureOperator F s ⇒ x ∈ s
    intro hx
    simp only [Finset.mem_subtype] at hx
    -- x.val ∈ I かつ I = s.map val
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, M, sval, I]
    obtain ⟨val, property⟩ := x
    dsimp only [closureOperator] at hx
    rw [Finset.map_eq_image] at hx
    simp at hx
    have :val ∈ finsetIntersection (Finset.filter (fun t ↦ F.sets t ∧ sval ⊆ t) F.ground.powerset):=
    by
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left,sval]
    have :val ∈ finsetIntersection M:=
    by
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, sval, M]
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left]--

  · -- (←) x ∈ s ⇒ x ∈ closureOperator F s
    intro hx
    let ef := extensive_from_SF_finset F s
    simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true, M, sval, I]
    obtain ⟨val, property⟩ := x
    exact ef hx

--集合から定義した作用素がidempotentを満たすこと。
lemma idempotent_from_SF_finset {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α)[DecidablePred F.sets] :
  ∀ s : Finset F.ground, closureOperator F s = closureOperator F (closureOperator F s) :=
by

  intro s
  -- 記号整理: T := closureOperator F s
  let T := closureOperator F s

  -- (1) T.map val は F.sets に属する (closureOperator_image_in_sets の適用)
  have T_inF : F.sets (T.image Subtype.val) :=
    closureOperator_image_in_sets F s

  -- (2) T はすでに「F.sets (T.map val) をみたす Finset F.ground」なので、
  --     idempotent_from_SF_finset_lem を使えば closureOperator F T = T
  have : closureOperator F T = T := by
    apply idempotent_from_SF_finset_lem F
    exact T_inF  -- T は F.sets に入っている

  -- (3) 結論:
  --     closureOperator F s = T
  --     ⇒ closureOperator F (closureOperator F s) = closureOperator F T = T
  --     ∴ closureOperator F s = closureOperator F (closureOperator F s)
  calc
    closureOperator F s
      = T                  := rfl
   _  = closureOperator F T := by rw [this]

--idempotent_from_SF_finset_lemの逆方向。ただし、closureOperator_image_in_setsとほぼ同じ。
lemma idempotent_from_SF_finset_lem_mpr
  {α : Type} [DecidableEq α] [Fintype α]
  (F : ClosureSystem α) [DecidablePred F.sets]
  : ∀ s :Finset F.ground, closureOperator F s = s → F.sets (s.image Subtype.val) :=
  by
    intro s h
    rw [← h]
    apply closureOperator_image_in_sets F --なぜかexactではだめ。


noncomputable def preclosure_operator_from_SF {α :Type} [DecidableEq α][Fintype α] (F: ClosureSystem α) [DecidablePred F.sets]: SetFamily.preclosure_operator F.ground :=
{
  cl := closureOperator F,
  extensive := extensive_from_SF_finset F,
  monotone := monotone_from_SF_finset F
}

noncomputable def closure_operator_from_SF {α :Type} [DecidableEq α][Fintype α] (F: ClosureSystem α) [DecidablePred F.sets]: SetFamily.closure_operator F.ground :=
{
  cl := closureOperator F,
  extensive := extensive_from_SF_finset F,
  monotone := monotone_from_SF_finset F,
  idempotent := idempotent_from_SF_finset F
}
---------------
----便利な補題等

--monotoneとidempotentを組み合わせて言えるので、特に補題にするほどでもないかもしれないが。closureと根付きサーキットの関係の定理で利用。
lemma closure_monotone_lemma {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α)[DecidablePred F.sets] (s : Finset F.ground) (t : Finset F.ground) :
  F.sets (t.image Subtype.val) → s ⊆ t → (closure_operator_from_SF F).cl s ⊆ t :=
by
  intro h st
  let cl := (closure_operator_from_SF F).cl
  have h_closure : cl s ⊆ cl t := monotone_from_SF_finset F s t st
  have : cl t = t :=
  by
     exact idempotent_from_SF_finset_lem F t h
  simp_all only [cl]

--closureの要素のclosureをしても、もとのものよりも広くならない。
lemma closure_singleton_lemma {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α)[DecidablePred F.sets] (s : Finset F.ground) (x : F.ground) :
  x ∈ closureOperator F s ↔ closureOperator F {x} ⊆ closureOperator F s :=
by
  apply Iff.intro
  · intro h
    let cl := (closure_operator_from_SF F).cl
    have h_closure : {x} ⊆ cl {x} := extensive_from_SF_finset F {x}
    have s_closed: F.sets (Finset.image Subtype.val (cl s)):=
    by
      exact closureOperator_image_in_sets F s
    have : {x} ⊆ cl s :=
    by
      simp_all only [Finset.singleton_subset_iff, cl]
      obtain ⟨val, property⟩ := x
      exact h

    have : cl ({x}) ⊆ (cl s) := by
      let cml := closure_monotone_lemma F {x} (cl s) s_closed this
      simp_all [cl]

    simp_all only [cl]
    exact this
  · intro h
    let cl := (closure_operator_from_SF F).cl
    have h_closure : {x} ⊆ cl {x} := extensive_from_SF_finset F {x}

    have : cl ({x}) ⊆ (cl s) := by
      dsimp [cl]
      simp_all only [Finset.singleton_subset_iff, cl]
      obtain ⟨val, property⟩ := x
      exact h

    have : {x} ⊆ cl s :=
    by
      exact Finset.Subset.trans h_closure this

    dsimp [cl] at this
    dsimp [closure_operator_from_SF] at this
    simp_all only [Finset.singleton_subset_iff, cl]

--hyperedgeでないもののclosureをとると真に大きくなるという補題。
lemma closure_ssubset {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α)[DecidablePred F.sets] (s : Finset F.ground) :
  ¬ F.sets (s.image Subtype.val) → s ⊂ closureOperator F s :=
by
  intro h
  let cl := (closure_operator_from_SF F).cl
  have h_closure : s ⊆ cl s := extensive_from_SF_finset F s
  have : s ≠ cl s :=
  by
    intro h1
    apply h
    apply idempotent_from_SF_finset_lem_mpr F s h1.symm
  simp_all only [cl]
  rw [@Finset.ssubset_iff_subset_ne]
  simp_all only [ne_eq]
  apply And.intro
  · exact h_closure
  · exact this
