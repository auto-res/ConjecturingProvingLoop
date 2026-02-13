

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P2 A := by
  intro hInt
  intro x hx
  have hEq : (interior (closure (interior A)) : Set X) = Set.univ := by
    simpa [hInt, closure_univ, interior_univ]
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hEq] using hx_univ

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → P2 A → P2 (A \ B) := by
  intro hB hP2A
  -- unfold the definition of `P2`
  unfold P2 at hP2A ⊢
  intro x hx
  -- split the hypothesis `x ∈ A \ B`
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∈ (Bᶜ : Set X) := hx.2
  -- from `P2 A`, obtain that `x` belongs to the open set
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- define the auxiliary open neighbourhood `U`
  set U : Set X := interior (closure (interior A)) ∩ Bᶜ with hUdef
  have hOpenU : IsOpen U := by
    simpa [hUdef] using (isOpen_interior).inter hB.isOpen_compl
  have hxU : x ∈ U := by
    simpa [hUdef] using And.intro hxIntA hxNotB
  -- show `U ⊆ closure (interior (A \ B))`
  have hUsubset : (U : Set X) ⊆ closure (interior (A \ B)) := by
    intro z hz
    rcases (show z ∈ U from hz) with ⟨hzIntA, hzNotB⟩
    -- `z` belongs to the closure of `interior A`
    have hzClIntA : z ∈ closure (interior A) := interior_subset hzIntA
    -- show that `z` is in the closure of `interior (A \ B)`
    have : z ∈ closure (interior (A \ B)) := by
      -- use the characterization of closure via neighbourhoods
      apply (mem_closure_iff).2
      intro W hW hzW
      -- consider the open set `W ∩ Bᶜ`
      have hOpen : IsOpen (W ∩ Bᶜ : Set X) := hW.inter hB.isOpen_compl
      have hzIn : z ∈ W ∩ Bᶜ := ⟨hzW, hzNotB⟩
      -- since `z ∈ closure (interior A)`, this intersection meets `interior A`
      have hNonempty :
          ((W ∩ Bᶜ) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hzClIntA _ hOpen hzIn
      rcases hNonempty with ⟨y, ⟨⟨hyW, hyNotB⟩, hyIntA⟩⟩
      -- `y` lies in `W`, in `interior A`, and outside `B`
      -- show that `y ∈ interior (A \ B)`
      have hyIntDiff : y ∈ interior (A \ B) := by
        -- open set contained in `A \ B`
        have hOpen' : IsOpen ((interior A) ∩ Bᶜ : Set X) :=
          (isOpen_interior).inter hB.isOpen_compl
        have hSub' : ((interior A) ∩ Bᶜ : Set X) ⊆ A \ B := by
          intro t ht
          exact ⟨(interior_subset) ht.1, ht.2⟩
        have hIncl := interior_maximal hSub' hOpen'
        exact hIncl ⟨hyIntA, hyNotB⟩
      -- hence, `W` meets `interior (A \ B)`
      exact ⟨y, ⟨hyW, hyIntDiff⟩⟩
    exact this
  -- `x` lies in the open set `U`, which is contained in the desired set
  have hInt := interior_maximal hUsubset hOpenU
  exact hInt hxU

theorem P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen (closure A) → P3 A := by
  intro hOpen
  intro x hx
  have hx' : (x : X) ∈ closure A := subset_closure hx
  simpa [hOpen.interior_eq] using hx'