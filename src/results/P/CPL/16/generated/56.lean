

theorem P3_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → P3 A → P3 (A \ B) := by
  intro hB hP3
  -- unfold the definition of `P3`
  unfold P3 at hP3 ⊢
  intro x hxDiff
  -- split the hypothesis `x ∈ A \ B`
  have hxA    : x ∈ A        := hxDiff.1
  have hxNotB : x ∈ (Bᶜ : Set X) := hxDiff.2
  -- from `P3 A`, obtain that `x` belongs to `interior (closure A)`
  have hxIntA : x ∈ interior (closure A) := hP3 hxA
  -- define the auxiliary open set `U`
  let U : Set X := interior (closure A) ∩ Bᶜ
  have hU_open : IsOpen (U : Set X) :=
    (isOpen_interior).inter hB.isOpen_compl
  have hxU : x ∈ U := by
    dsimp [U] ; exact ⟨hxIntA, hxNotB⟩
  -- show `U ⊆ closure (A \ B)`
  have hUsubset : (U : Set X) ⊆ closure (A \ B) := by
    intro z hzU
    have hzIntA : z ∈ interior (closure A) := hzU.1
    have hzNotB : z ∈ (Bᶜ : Set X)         := hzU.2
    have hzClA  : z ∈ closure A            := interior_subset hzIntA
    -- neighbourhood criterion for the closure
    apply (mem_closure_iff).2
    intro V hV hzV
    -- refine the neighbourhood so that it is disjoint from `B`
    have hV₁_open : IsOpen (V ∩ Bᶜ : Set X) := hV.inter hB.isOpen_compl
    have hzV₁     : z ∈ V ∩ Bᶜ := ⟨hzV, hzNotB⟩
    -- since `z ∈ closure A`, this refined neighbourhood meets `A`
    have hNonempty : ((V ∩ Bᶜ) ∩ A).Nonempty :=
      (mem_closure_iff).1 hzClA _ hV₁_open hzV₁
    rcases hNonempty with ⟨y, ⟨⟨hyV, hyNotB⟩, hyA⟩⟩
    -- `y` lies in `V ∩ (A \ B)`
    exact ⟨y, ⟨hyV, ⟨hyA, hyNotB⟩⟩⟩
  -- `U` is an open nbrhood of `x` contained in the desired set
  exact (interior_maximal hUsubset hU_open) hxU