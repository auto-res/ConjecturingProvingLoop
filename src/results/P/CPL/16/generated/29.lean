

theorem P1_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} : IsClosed B → P1 A → P1 (A \ B) := by
  intro hB hP1
  -- we prove that every point of `A \ B` belongs to the closure of `interior (A \ B)`
  unfold P1 at hP1 ⊢
  intro x hxDiff
  -- from `P1 A`
  have hCl : x ∈ closure (interior A) := hP1 hxDiff.1
  -- use the neighbourhood characterization of the closure
  apply (mem_closure_iff).2
  intro U hU hxU
  -- refine the neighbourhood so that it is disjoint from `B`
  have hVopen : IsOpen (U ∩ (Bᶜ) : Set X) := hU.inter hB.isOpen_compl
  have hxV : x ∈ (U ∩ (Bᶜ) : Set X) := by
    refine ⟨hxU, hxDiff.2⟩
  -- since `x` is in the closure of `interior A`, the refined neighbourhood
  -- meets `interior A`
  have hNonempty : ((U ∩ (Bᶜ)) ∩ interior A).Nonempty := by
    have := (mem_closure_iff).1 hCl _ hVopen hxV
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using this
  rcases hNonempty with ⟨y, ⟨⟨hyU, hyNotB⟩, hyIntA⟩⟩
  -- the point `y` is in `interior A` and outside `B`; hence it belongs to
  -- `interior (A \ B)`
  have hyIntDiff : y ∈ interior (A \ B) := by
    -- the open set `interior A ∩ Bᶜ` is contained in `A \ B`
    have hOpen : IsOpen ((interior A) ∩ (Bᶜ) : Set X) :=
      (isOpen_interior).inter hB.isOpen_compl
    have hSub : ((interior A) ∩ (Bᶜ) : Set X) ⊆ A \ B := by
      intro z hz
      rcases hz with ⟨hzIntA, hzNotB⟩
      exact ⟨(interior_subset) hzIntA, hzNotB⟩
    have hIncl := interior_maximal hSub hOpen
    exact hIncl ⟨hyIntA, hyNotB⟩
  -- `y` is the required point in `U ∩ interior (A \ B)`
  exact ⟨y, hyU, hyIntDiff⟩

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  have h1 : P1 A ↔ P2 A := (P2_iff_P1_of_open (A := A) hA).symm
  have h2 : P2 A ↔ P3 A := (P3_iff_P2_of_open (A := A) hA).symm
  exact h1.trans h2