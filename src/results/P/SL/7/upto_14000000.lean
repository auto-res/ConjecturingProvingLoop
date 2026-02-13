

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro h
  have h' : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact Set.Subset.trans h h'

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  have h' : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact Set.Subset.trans h h'

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro h
  exact ⟨Topology.P2_implies_P1 h, Topology.P2_implies_P3 h⟩

theorem IsOpen_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  simpa [Topology.P2, hA.interior_eq] using interior_maximal subset_closure hA

theorem IsOpen_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P3 A := by
  have hP2 : Topology.P2 A := IsOpen_P2 hA
  exact Topology.P2_implies_P1_and_P3 hP2

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure A = (Set.univ : Set X)) : Topology.P3 A := by
  have hint : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA] using (isOpen_univ.interior_eq)
  simpa [Topology.P3, hint] using (Set.subset_univ (A := A))

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = (Set.univ : Set X)) : Topology.P2 A := by
  have hInt : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hA] using (isOpen_univ.interior_eq)
  simpa [Topology.P2, hInt] using (Set.subset_univ (A := A))

theorem Topology.P1_closed_iff_closureInterior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P1 A ↔ closure (interior A) = A := by
  unfold Topology.P1
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    ·
      have : closure (interior A) ⊆ closure A := closure_mono interior_subset
      simpa [hA.closure_eq] using this
    · exact hP1
  · intro hEq
    simpa [hEq] using (Set.Subset.rfl : A ⊆ A)

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = (Set.univ : Set X)) : Topology.P1 A := by
  simpa [Topology.P1, hA] using (Set.subset_univ (A := A))

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hx_closureA
  | inr hxB =>
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      have hSub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_right
      exact hSub hx_closureB

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure A) := hA hxA
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hx_intA
  | inr hxB =>
      have hx_intB : x ∈ interior (closure B) := hB hxB
      have hSub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_right
      exact hSub hx_intB

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ interior (closure (interior A)) := hA hxA
      have hSub : interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hx₁
  | inr hxB =>
      have hx₁ : x ∈ interior (closure (interior B)) := hB hxB
      have hSub : interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact hSub hx₁

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  have h := (IsOpen_P1_and_P3 (A := interior A) isOpen_interior).2
  simpa using h

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  exact closure_mono hP3

theorem Topology.P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    -- From P3 and closedness we deduce openness.
    have hsub : (A : Set X) ⊆ interior A := by
      simpa [Topology.P3, hA.closure_eq] using hP3
    have hEq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hsub
    have : IsOpen (interior A) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    exact (IsOpen_P1_and_P3 (A := A) hOpen).2

theorem Topology.interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) : (interior A).Nonempty := by
  classical
  by_contra hIntEmpty
  have hIntEq : interior A = (∅ : Set X) := by
    simpa [Set.not_nonempty_iff_eq_empty] using hIntEmpty
  have hClosureEq : closure (interior A) = (∅ : Set X) := by
    simpa [hIntEq] using
      (closure_empty : closure (∅ : Set X) = (∅ : Set X))
  rcases hA with ⟨x, hx⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  have : x ∈ (∅ : Set X) := by
    simpa [hClosureEq] using hx_cl
  cases this

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  simpa using (IsOpen_P2 (A := interior A) isOpen_interior)

theorem Topology.P1_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → (B ⊆ closure (interior A)) → Topology.P1 (A ∪ B) := by
  intro hP1A hBsubset
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_clA : x ∈ closure (interior A) := hP1A hxA
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hx_clA
  | inr hxB =>
      have hx_clA : x ∈ closure (interior A) := hBsubset hxB
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hx_clA

theorem Topology.P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    intro x hx
    cases hx
  · dsimp [Topology.P2]
    intro x hx
    cases hx
  · dsimp [Topology.P3]
    intro x hx
    cases hx

theorem Topology.P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    intro x hx
    simpa [interior_univ, closure_univ] using hx
  · dsimp [Topology.P2]
    intro x hx
    simpa [interior_univ, closure_univ] using hx
  · dsimp [Topology.P3]
    intro x hx
    simpa [interior_univ, closure_univ] using hx

theorem Topology.P1_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  have hOpen : IsOpen A := (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
  exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen).1

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro hP3
    dsimp [Topology.P2]
    dsimp [Topology.P3] at hP3
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    have hEq : interior (closure (interior A)) = interior (closure A) := by
      simpa [hInt]
    simpa [hEq] using hx'

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro hP3
    have hOpen : IsOpen A := (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
    exact (IsOpen_P2 (A := A) hOpen)

theorem Topology.interiorClosureInterior_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    (A : Set X) : interior (closure (interior A)) ⊆ interior (closure A) := by
  exact interior_mono (closure_mono interior_subset)

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  have h := Topology.IsOpen_P1_and_P3 (A := A) hA
  exact ⟨fun _ => h.2, fun _ => h.1⟩

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  have h₁ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  simpa using h₁.trans h₂.symm

theorem Topology.P2_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ IsOpen A := by
  have h₁ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isClosed (A := A) hA
  have h₂ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  simpa using h₁.trans h₂

theorem Topology.P1_iff_closure_eq_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  unfold Topology.P1
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    ·
      have h₁ : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
      simpa [closure_closure] using h₁
    · exact closure_mono interior_subset
  · intro hEq
    simpa [Topology.P1, hEq] using (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.P1_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact (Topology.IsOpen_P1_and_P3 (A := interior (closure A)) hOpen).1

theorem Topology.P1_iff_exists_open_dense_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ closure U = closure A := by
  classical
  have hEq := Topology.P1_iff_closure_eq_closureInterior (A := A)
  constructor
  · intro hP1
    refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
    have h : closure A = closure (interior A) := (hEq).1 hP1
    exact h.symm
  · rintro ⟨U, hU_open, hU_subset, hClosureEq⟩
    dsimp [Topology.P1]
    intro x hxA
    have hx_closureU : x ∈ closure U := by
      have hx_closureA : x ∈ closure A := subset_closure hxA
      simpa [hClosureEq.symm] using hx_closureA
    have hU_subset_int : U ⊆ interior A := by
      intro y hyU
      have hy_intU : y ∈ interior U := by
        simpa [hU_open.interior_eq] using hyU
      exact (interior_mono hU_subset) hy_intU
    have hClosure_subset : closure U ⊆ closure (interior A) := closure_mono hU_subset_int
    exact hClosure_subset hx_closureU

theorem Topology.P3_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact (Topology.IsOpen_P1_and_P3 (A := interior (closure A)) hOpen).2

theorem Topology.P2_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact (IsOpen_P2 (A := interior (closure A)) hOpen)

theorem Topology.IsOpen_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP2 : Topology.P2 A := (Topology.IsOpen_P2 (A := A) hA)
  have hP1P3 : Topology.P1 A ∧ Topology.P3 A := (Topology.IsOpen_P1_and_P3 (A := A) hA)
  exact ⟨hP1P3.1, hP2, hP1P3.2⟩

theorem Topology.closureInterior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) : closure (interior A) = closure A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  have hEq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  simpa using hEq.symm

theorem Topology.interiorClosureInterior_eq_interiorClosure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (∀ i, Topology.P1 (F i)) → Topology.P1 (⋃ i, F i) := by
  classical
  intro hF
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_closureFi : x ∈ closure (interior (F i)) := hF i hxFi
  have hSub : closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hx_closureFi

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (∀ i, Topology.P3 (F i)) → Topology.P3 (⋃ i, F i) := by
  classical
  intro hF
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_intFi : x ∈ interior (closure (F i)) := hF i hxFi
  have hSub : interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) := by
    apply interior_mono
    have : (closure (F i)) ⊆ closure (⋃ j, F j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hSub hx_intFi

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (∀ i, Topology.P2 (F i)) → Topology.P2 (⋃ i, F i) := by
  classical
  intro hF
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hx_intFi : x ∈ interior (closure (interior (F i))) := hF i hxFi
  have hSub : interior (closure (interior (F i))) ⊆
      interior (closure (interior (⋃ j, F j))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hx_intFi

theorem Topology.closureInterior_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    (A : Set X) : closure (interior A) ⊆ closure (interior (closure A)) := by
  exact closure_mono (interior_mono subset_closure)

theorem Topology.IsOpen_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  exact (Topology.IsOpen_P1_and_P3 (A := A) hA).1

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.P3_implies_P1_closure hP3

theorem Topology.P1_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior A` is open and contained in its closure
  have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    exact interior_maximal (subset_closure) isOpen_interior
  -- Taking closures preserves the inclusion
  have h_closure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    exact closure_mono h_subset
  exact h_closure hx

theorem Topology.P3_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hP3A hP3B
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_isOpen (A := B) hB).1 hP3B
  have hOpenAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  have hClosedAB : IsClosed (A ∩ B) := hA.inter hB
  exact
    (Topology.P3_closed_iff_isOpen (A := A ∩ B) hClosedAB).2 hOpenAB

theorem Topology.interiorClosureInterior_eq_interiorClosure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    interior (closure (interior A)) = interior (closure A) := by
  have hClosureEq : closure (interior A) = closure A :=
    Topology.closureInterior_eq_closure_of_P2 (A := A) hP2
  simpa [hClosureEq] using
    (rfl : interior (closure (interior A)) =
      interior (closure (interior A)))

theorem Topology.P3_closure_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using (Topology.P3_closed_iff_isOpen (A := closure A) hClosed)

theorem Topology.P2_closure_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using (Topology.P2_closed_iff_isOpen (A := closure A) hClosed)

theorem Topology.closureInterior_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.interiorClosureInterior_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (interior A))) = interior (closure (interior A)) := by
  simpa [interior_interior]

theorem Topology.P2_closureInterior_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using (Topology.P2_closed_iff_isOpen (A := closure (interior A)) hClosed)

theorem Topology.IsOpen_P1_P2_P3_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.IsOpen_P1_P2_P3 (A := A ∩ B) hOpen)

theorem Set.Subset_univ {α : Type*} (A : Set α) : A ⊆ (Set.univ : Set α) := by
  intro x _
  trivial

theorem Topology.P3_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact (Topology.IsOpen_P1_and_P3 (A := interior (closure (interior A))) hOpen).2

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A) = (Set.univ : Set X)) : Topology.P3 A := by
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hA
  exact Topology.P2_implies_P3 hP2

theorem Topology.interiorClosure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem Topology.interiorClosureInterior_subset_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_cl : x ∈ closure (interior A) := interior_subset hx
  exact (Topology.closureInterior_subset_closureInteriorClosure (A := A)) hx_cl

theorem interiorClosureInterior_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  exact interior_mono (closure_mono (interior_subset (s := A)))

theorem Topology.closureInterior_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hSub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_left
      exact hSub hxA
  | inr hxB =>
      have hSub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono Set.subset_union_right
      exact hSub hxB

theorem Topology.interior_subset_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    (A : Set X) : interior A ⊆ interior (closure (interior A)) := by
  -- First, note that `interior A` is contained in its closure.
  have hSub : (interior A : Set X) ⊆ closure (interior A) := by
    intro x hx
    exact subset_closure hx
  -- Monotonicity of `interior` gives the desired inclusion.
  have h := interior_mono hSub
  simpa [interior_interior] using h

theorem Topology.P1_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact (Topology.IsOpen_P1_and_P3 (A := interior (closure (interior A))) hOpen).1

theorem Topology.P3_closureInterior_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen (A := closure (interior A)) hClosed)

theorem Topology.P3_iff_exists_open_superset_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  classical
  unfold Topology.P3
  constructor
  · intro hP3
    exact ⟨interior (closure A), isOpen_interior, hP3, interior_subset⟩
  · rintro ⟨U, hU_open, hA_subU, hU_sub_cl⟩
    have hU_sub_int : U ⊆ interior (closure A) := interior_maximal hU_sub_cl hU_open
    intro x hxA
    exact hU_sub_int (hA_subU hxA)

theorem Topology.interiorClosureInterior_eq_interiorClosure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure (interior A)) = interior (closure A) := by
  -- From `P1` we obtain the equality of closures
  have hEq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  -- Applying `interior` to both sides yields the desired equality
  have hInt : interior (closure A) = interior (closure (interior A)) :=
    congrArg interior hEq
  simpa using hInt.symm

theorem Topology.interiorClosureInterior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  exact interior_mono (closure_mono (interior_mono hAB))

theorem Topology.interiorClosure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  constructor
  · intro hP1
    exact ⟨h₁.mp hP1, h₂.mp hP1⟩
  · rintro ⟨hP2, _hP3⟩
    exact h₁.mpr hP2

theorem Topology.interiorClosure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hxA
  | inr hxB =>
      have hSub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_right
      exact hSub hxB

theorem Topology.closureInteriorClosureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h : interior (closure (interior A)) ⊆ closure (interior A) := by
      exact interior_subset
    have h' := closure_mono h
    simpa [closure_closure] using h'
  ·
    have h : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interiorClosureInterior (A := A)
    have h' := closure_mono h
    simpa [closure_closure] using h'

theorem Topology.P3_singleton_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P3 ({x} : Set X) ↔ IsOpen ({x} : Set X) := by
  have hClosed : IsClosed ({x} : Set X) := isClosed_singleton
  simpa using (Topology.P3_closed_iff_isOpen (A := ({x} : Set X)) hClosed)

theorem Topology.P2_singleton_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P2 ({x} : Set X) ↔ IsOpen ({x} : Set X) := by
  have hClosed : IsClosed ({x} : Set X) := isClosed_singleton
  simpa using (Topology.P2_closed_iff_isOpen (A := ({x} : Set X)) hClosed)

theorem Topology.P2_inter_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hP2A hP2B
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (A := A) hA).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_isOpen (A := B) hB).1 hP2B
  have hOpenAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  exact IsOpen_P2 (A := A ∩ B) hOpenAB

theorem Topology.interiorClosure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show membership in `interior (closure A)`
  have hLeft : x ∈ interior (closure A) := by
    have hSub : interior (closure (A ∩ B)) ⊆ interior (closure A) := by
      apply interior_mono
      have : closure (A ∩ B) ⊆ closure A := by
        apply closure_mono
        exact Set.inter_subset_left
      exact this
    exact hSub hx
  -- Show membership in `interior (closure B)`
  have hRight : x ∈ interior (closure B) := by
    have hSub : interior (closure (A ∩ B)) ⊆ interior (closure B) := by
      apply interior_mono
      have : closure (A ∩ B) ⊆ closure B := by
        apply closure_mono
        exact Set.inter_subset_right
      exact this
    exact hSub hx
  exact ⟨hLeft, hRight⟩

theorem Topology.closureInterior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
    apply closure_mono
    apply interior_mono
    exact Set.inter_subset_left
  have hB : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
    apply closure_mono
    apply interior_mono
    exact Set.inter_subset_right
  exact ⟨hA hx, hB hx⟩

theorem Topology.P3_closure_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure (A : Set X) := by
  have hEquiv := (Topology.P3_closure_iff_isOpen (A := A))
  constructor
  · intro hP3
    have hOpen : IsOpen (closure (A : Set X)) := (hEquiv).1 hP3
    simpa using hOpen.interior_eq
  · intro hIntEq
    have hOpen : IsOpen (closure (A : Set X)) := by
      have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
      simpa [hIntEq] using this
    exact (hEquiv).2 hOpen

theorem Topology.closureInterior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.P1_singleton_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P1 ({x} : Set X) ↔ IsOpen ({x} : Set X) := by
  constructor
  · intro hP1
    -- First, show that `interior {x}` is non-empty.
    have hIntNonempty : (interior ({x} : Set X)).Nonempty := by
      classical
      by_contra hEmpty
      have hIntEq : interior ({x} : Set X) = (∅ : Set X) := by
        simpa [Set.not_nonempty_iff_eq_empty] using hEmpty
      have hClosureEq : closure (interior ({x} : Set X)) = (∅ : Set X) := by
        simpa [hIntEq] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))
      have hx_cl : (x : X) ∈ closure (interior ({x} : Set X)) := by
        have : (x : X) ∈ ({x} : Set X) := by
          simp
        exact hP1 this
      have : (x : X) ∈ (∅ : Set X) := by
        simpa [hClosureEq] using hx_cl
      exact this
    -- Obtain a point of the interior; it must be `x`.
    rcases hIntNonempty with ⟨y, hy⟩
    have hysingleton : y = x := by
      have : y ∈ ({x} : Set X) := (interior_subset : interior ({x} : Set X) ⊆ {x}) hy
      simpa [Set.mem_singleton_iff] using this
    have hxInt : (x : X) ∈ interior ({x} : Set X) := by
      simpa [hysingleton] using hy
    -- Hence `interior {x} = {x}`.
    have hSubset : ({x} : Set X) ⊆ interior ({x} : Set X) := by
      intro z hz
      have : z = x := by
        simpa [Set.mem_singleton_iff] using hz
      simpa [this] using hxInt
    have hIntEq : interior ({x} : Set X) = ({x} : Set X) := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact hSubset
    -- Therefore `{x}` is open.
    have : IsOpen (interior ({x} : Set X)) := isOpen_interior
    simpa [hIntEq] using this
  · intro hOpen
    exact Topology.IsOpen_P1 (A := ({x} : Set X)) hOpen

theorem Topology.P2_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact IsOpen_P2 (A := interior (closure (interior A))) hOpen

theorem Topology.interiorClosureInterior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` : from left to right.
    have hSub : closure (interior A) ⊆ A := by
      have : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hA.closure_eq] using this
    exact interior_mono hSub
  · -- `⊇` : from right to left.
    have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono hSub
    simpa [interior_interior] using this

theorem Topology.interiorClosureInterior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  exact ⟨x, hP2 hxA⟩

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hx
  have : (x : X) ∈ interior (closure (closure (A : Set X))) :=
    hP3 (subset_closure hx)
  simpa [closure_closure] using this

theorem Topology.interior_subset_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ interior (closure A) := by
  simpa using interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.P2_iff_P3_of_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  have h₁ := (Topology.P2_closed_iff_isOpen (A := closure (A : Set X)) hClosed)
  have h₂ := (Topology.P3_closed_iff_isOpen (A := closure (A : Set X)) hClosed)
  exact h₁.trans h₂.symm



theorem Topology.P3_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → (B ⊆ interior (closure A)) → Topology.P3 (A ∪ B) := by
  intro hP3A hBsubset
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure A) := hP3A hxA
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hx_intA
  | inr hxB =>
      have hx_intA : x ∈ interior (closure A) := hBsubset hxB
      have hSub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        apply interior_mono
        exact closure_mono Set.subset_union_left
      exact hSub hx_intA

theorem Topology.P1_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) : Topology.P1 A := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
  exact Topology.P1_of_P3_closed (A := A) hA hP3

theorem Topology.P2_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → (B ⊆ interior (closure (interior A))) → Topology.P2 (A ∪ B) := by
  intro hP2A hBsubset
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_intA : x ∈ interior (closure (interior A)) := hP2A hxA
      have hSub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hx_intA
  | inr hxB =>
      have hx_intA : x ∈ interior (closure (interior A)) := hBsubset hxB
      have hSub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hx_intA

theorem Topology.P3_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P3 A := by
  -- First, translate the openness of `closure A` into `P3 (closure A)`.
  have hP3_closure : Topology.P3 (closure (A : Set X)) := by
    have hEquiv := (Topology.P3_closure_iff_isOpen (A := A))
    exact (hEquiv).2 hOpen
  -- Then use `P3 (closure A)` to obtain `P3 A`.
  exact Topology.P3_of_P3_closure (A := A) hP3_closure

theorem Topology.P1_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure A)) := by
  intro hP1 x hxA
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  have hIncl : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closureInterior_subset_closureInteriorClosure (A := A)
  exact hIncl hx_cl

theorem Topology.closureInterior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : closure (interior A) = closure A := by
  have hP2 : Topology.P2 A := IsOpen_P2 (A := A) hA
  simpa using Topology.closureInterior_eq_closure_of_P2 (A := A) hP2

theorem Topology.closure_eq_univ_of_P1_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A)
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  simpa using hEq.trans hDense

theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP2 : Topology.P2 A := Topology.IsOpen_P2 (A := A) hA
  exact Topology.P2_implies_P1_closure (A := A) hP2

theorem Topology.interiorClosureInterior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) = interior (closure (interior A)) := by
  have h := Topology.closureInteriorClosureInterior_eq_closureInterior (A := A)
  simpa using congrArg interior h

theorem Topology.interiorClosure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interiorClosureInterior_subset_interiorClosure (A := closure A)
    simpa [closure_closure] using h
  ·
    have h :
        interior (closure A) ⊆
          interior (closure (interior (closure A))) :=
      Topology.interior_subset_interiorClosureInterior (A := closure A)
    simpa using h

theorem Topology.closure_eq_closureInteriorClosure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  apply Set.Subset.antisymm
  ·
    have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    simpa using (closure_mono hSub)
  ·
    have hSub : (interior (closure (A : Set X)) : Set X) ⊆ closure (A : Set X) :=
      interior_subset
    simpa using (closure_mono hSub)

theorem Topology.closureInteriorClosureInteriorClosure_eq_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closureInteriorClosureInterior_eq_closureInterior (A := closure A))

theorem Topology.P3_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P3 F ↔ IsOpen F := by
  have hClosed : IsClosed (F : Set X) := by
    exact hF.isClosed
  simpa using (Topology.P3_closed_iff_isOpen (A := F) hClosed)

theorem Topology.P2_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P2 F ↔ IsOpen F := by
  have hClosed : IsClosed (F : Set X) := hF.isClosed
  simpa using (Topology.P2_closed_iff_isOpen (A := F) hClosed)

theorem Topology.P1_P2_P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA.isOpen_compl
  simpa using (Topology.IsOpen_P1_P2_P3 (A := Aᶜ) hOpen)

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure (A : Set X)) := by
  intro hP1
  dsimp [Topology.P1] at *
  intro x hx_clA
  -- From `P1 A` we have `closure A = closure (interior A)`.
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  -- Rewriting `hx_clA` using this equality yields membership in `closure (interior A)`.
  have hx_clIntA : x ∈ closure (interior A) := by
    simpa [hEq] using hx_clA
  -- Monotonicity of `interior` and `closure` gives the required inclusion.
  have hSub :
      closure (interior A) ⊆ closure (interior (closure (A : Set X))) :=
    Topology.closureInterior_subset_closureInteriorClosure (A := A)
  exact hSub hx_clIntA

theorem Topology.closureInteriorClosure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  exact closure_mono (interior_mono (closure_mono hAB))

theorem Topology.closure_eq_univ_iff_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro h
    simpa [h] using (isOpen_univ.interior_eq)
  · intro h
    -- `interior (closure A)` is contained in `closure A`.
    have hSub : (interior (closure (A : Set X)) : Set X) ⊆ closure (A : Set X) :=
      interior_subset
    -- Using `h`, this becomes `univ ⊆ closure A`.
    have h' : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [h] using hSub
    -- The reverse inclusion is trivial.
    have h'' : closure (A : Set X) ⊆ (Set.univ : Set X) := Set.Subset_univ _
    exact Set.Subset.antisymm h'' h'

theorem Topology.interiorClosure_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure (A : Set X)) = interior A := by
  simpa [hA.closure_eq]

theorem Topology.closureInterior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) : closure (interior A) ⊆ closure (A : Set X) := by
  simpa using (closure_mono (interior_subset : interior A ⊆ A))

theorem Topology.P2_and_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    (Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  have hP2 := Topology.P2_closed_iff_isOpen (A := A) hA
  have hP3 := Topology.P3_closed_iff_isOpen (A := A) hA
  constructor
  · intro h
    exact (hP2).1 h.1
  · intro hOpen
    exact ⟨(hP2).2 hOpen, (hP3).2 hOpen⟩

theorem Topology.P1_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- `interior (closure A)` is contained in `interior (closure (interior (closure A)))`
  have h_subset :
      (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) := by
    simpa using
      (Topology.interior_subset_interiorClosureInterior (A := closure A))
  -- Taking closures preserves the inclusion
  have h_closure :
      closure (interior (closure A)) ⊆
        closure (interior (closure (interior (closure A)))) :=
    closure_mono h_subset
  exact h_closure hx



theorem Topology.closureInteriorClosure_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
  -- `interior (closure A)` is contained in `closure A`.
  have hSub : (interior (closure (A : Set X)) : Set X) ⊆ closure (A : Set X) :=
    interior_subset
  -- Taking closures preserves the inclusion.
  have hClosure :
      closure (interior (closure (A : Set X))) ⊆ closure (closure (A : Set X)) :=
    closure_mono hSub
  -- Simplify the right-hand side using idempotency of `closure`.
  simpa [closure_closure] using hClosure

theorem Topology.interiorClosureInterior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior A)) ⊆ closure (A : Set X) := by
  -- First, we use the established inclusion
  -- `interior (closure (interior A)) ⊆ interior (closure A)`.
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interiorClosureInterior_subset_interiorClosure (A := A)
  -- Next, we recall that `interior (closure A)` is contained in `closure A`.
  have h₂ : interior (closure A) ⊆ closure A := interior_subset
  -- Chaining the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂

theorem IsOpen_P2' {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A := by
  -- Unfold the definition of `P2`.
  dsimp [Topology.P2]
  -- Prove the inclusion pointwise.
  intro x hxA
  -- Since `A` is open, we can place `x` inside `interior (closure A)`.
  have hx_in_int_closureA : x ∈ interior (closure A) := by
    have hIncl : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal subset_closure hA
    exact hIncl hxA
  -- Relate `interior (closure (interior A))` to `interior (closure A)`
  -- using the fact that `interior A = A`.
  have hEq : interior (closure (interior A)) = interior (closure A) := by
    simpa [hA.interior_eq]
  -- Rewrite and finish.
  simpa [hEq] using hx_in_int_closureA

theorem Topology.P3_union_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P3 A → IsOpen U → Topology.P3 (A ∪ U) := by
  intro hP3A hU_open
  have hP3U : Topology.P3 U := (Topology.IsOpen_P1_and_P3 (A := U) hU_open).2
  exact Topology.P3_union hP3A hP3U

theorem Topology.closureInteriorClosure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (closure A)) ∪ closure (interior (closure B)) ⊆
      closure (interior (closure (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : closure (interior (closure A)) ⊆
          closure (interior (closure (A ∪ B))) := by
        apply closure_mono
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_left
      exact hSub hA
  | inr hB =>
      have hSub : closure (interior (closure B)) ⊆
          closure (interior (closure (A ∪ B))) := by
        apply closure_mono
        apply interior_mono
        apply closure_mono
        exact Set.subset_union_right
      exact hSub hB

theorem Topology.interiorClosure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hx
  exact subset_closure hx

theorem Topology.P2_iff_P3_of_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ := (Topology.P2_closureInterior_iff_isOpen (A := A))
  have h₂ := (Topology.P3_closureInterior_iff_isOpen (A := A))
  simpa using h₁.trans h₂.symm

theorem Topology.P1_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P1 F ↔ IsOpen F := by
  have hClosedF : IsClosed (F : Set X) := hF.isClosed
  constructor
  · intro hP1
    -- From `P1` and closedness obtain `closure (interior F) = F`.
    have hEq₁ : closure (interior F) = (F : Set X) :=
      (Topology.P1_closed_iff_closureInterior_eq (A := F) hClosedF).1 hP1
    -- `interior F` is finite, hence closed, so its closure is itself.
    have hClosedInt : IsClosed (interior F) := (hF.subset interior_subset).isClosed
    have hEq₂ : closure (interior F) = interior F := hClosedInt.closure_eq
    -- Combining the equalities gives `interior F = F`.
    have hIntEq : interior F = (F : Set X) := by
      calc
        interior F = closure (interior F) := by
          simpa [hEq₂]
        _ = F := hEq₁
    -- Therefore `F` is open.
    have : IsOpen (interior F) := isOpen_interior
    simpa [hIntEq] using this
  · intro hOpenF
    exact Topology.IsOpen_P1 (A := F) hOpenF

theorem Topology.P2_iff_exists_open_superset_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  classical
  -- Unfold the definition of `P2`.
  unfold Topology.P2
  constructor
  · intro hP2
    -- Choose `U = interior (closure (interior A))`.
    refine ⟨interior (closure (interior A)), isOpen_interior, hP2, ?_⟩
    exact Set.Subset.rfl
  · rintro ⟨U, _hU_open, hA_subU, hU_sub⟩
    -- Use the two inclusions to obtain the desired one.
    intro x hxA
    exact hU_sub (hA_subU hxA)

theorem Topology.P1_iff_closure_subset_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure (A : Set X) ⊆ closure (interior A) := by
  unfold Topology.P1
  constructor
  · intro hP1
    have h : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using h
  · intro hSub
    intro x hxA
    have hx_closureA : x ∈ closure (A : Set X) := subset_closure hxA
    exact hSub hx_closureA

theorem Topology.interiorClosureInterior_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  simpa using
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A))

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2cl
  -- From `P2 (closure A)` and closedness of `closure A`, we get that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hEquiv := (Topology.P2_closure_iff_isOpen (A := A))
    exact (hEquiv).1 hP2cl
  -- Openness of `closure A` yields `P3 A`.
  exact Topology.P3_of_open_closure (A := A) hOpen

theorem Topology.interior_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) :
    interior (A : Set X) = A := by
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
  simpa using hOpen.interior_eq

theorem Topology.P1_of_closureInterior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (A : Set X)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  simpa [h] using hx

theorem Topology.P2_union_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P2 A → IsOpen U → Topology.P2 (A ∪ U) := by
  intro hP2A hUopen
  have hP2U : Topology.P2 U := IsOpen_P2 (A := U) hUopen
  exact Topology.P2_union (A := A) (B := U) hP2A hP2U

theorem Topology.P3_of_dense_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) : Topology.P3 A := by
  simpa [Topology.P3, h] using (Set.subset_univ (A := A))

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  exact (Topology.P1_P2_P3_empty (X := X)).1

theorem Topology.P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ interior (A : Set X) = A := by
  constructor
  · intro hP3
    exact Topology.interior_eq_of_P3_closed (A := A) hA hP3
  · intro hInt
    -- From `interior A = A` we get that `A` is open.
    have hOpen : IsOpen A := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hInt] using this
    -- An open set satisfies `P3`.
    exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen).2

theorem Topology.P1_union_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P1 A → IsOpen U → Topology.P1 (A ∪ U) := by
  intro hP1A hUopen
  have hP1U : Topology.P1 U := Topology.IsOpen_P1 (A := U) hUopen
  exact Topology.P1_union (A := A) (B := U) hP1A hP1U

theorem Topology.interiorClosureClosure_eq_interiorClosure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [closure_closure]

theorem Topology.subset_closureInterior_of_subset_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1 : Topology.P1 B) :
    A ⊆ closure (interior B) := by
  intro x hxA
  exact hP1 (hAB hxA)

theorem Topology.interiorClosure_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  -- First, obtain a point in `interior A` using `P1`.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hA
  -- The inclusion `interior A ⊆ interior (closure A)` moves this point into the desired set.
  have hIncl : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interiorClosure (A := A)
  rcases hIntA with ⟨x, hx⟩
  exact ⟨x, hIncl hx⟩

theorem Topology.interiorClosureInterior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (interior (closure (interior A))).Nonempty := by
  -- Obtain a point in `interior A` from `P1` and the nonemptiness of `A`.
  have hIntA : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hA
  -- `interior A` is contained in `interior (closure (interior A))`.
  have hIncl : interior A ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interiorClosureInterior (A := A)
  -- Transport the point along the inclusion.
  rcases hIntA with ⟨x, hx⟩
  exact ⟨x, hIncl hx⟩

theorem Topology.P1_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P1 A → IsOpen U → Topology.P1 (A ∩ U) := by
  intro hP1A hUopen
  -- Unfold the goal definition of `P1`.
  dsimp [Topology.P1] at *
  intro x hxAU
  -- Split membership in the intersection.
  rcases hxAU with ⟨hxA, hxU⟩
  -- From `P1 A` we already have membership in `closure (interior A)`.
  have hx_closure_intA : x ∈ closure (interior A) := hP1A hxA
  -- We first prove that `x ∈ closure (interior A ∩ U)`.
  have hx_closure_intA_U : x ∈ closure (interior A ∩ U) := by
    -- Use the neighbourhood characterisation of closures.
    have hClosure := (mem_closure_iff).1 hx_closure_intA
    -- Show that every open neighbourhood `V` of `x` meets `interior A ∩ U`.
    have : ∀ V, IsOpen V → x ∈ V → (V ∩ (interior A ∩ U)).Nonempty := by
      intro V hVopen hxV
      -- Work with `V ∩ U`, still an open neighbourhood of `x`.
      have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
      have hxVU : x ∈ V ∩ U := ⟨hxV, hxU⟩
      -- This neighbourhood meets `interior A` by definition of closure.
      have hNonempty : (V ∩ U ∩ interior A).Nonempty :=
        hClosure _ hVUopen hxVU
      -- Re-arrange intersections.
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using hNonempty
    -- Re-assemble the closure information.
    exact (mem_closure_iff).2 this
  -- Next, relate `interior A ∩ U` to `interior (A ∩ U)`.
  have hSub : (interior A ∩ U : Set X) ⊆ interior (A ∩ U) := by
    -- `interior A ∩ U` is open.
    have hOpen : IsOpen (interior A ∩ U) := (isOpen_interior).inter hUopen
    -- It is contained in `A ∩ U`.
    have hIncl : (interior A ∩ U : Set X) ⊆ A ∩ U := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    -- Use the maximality property of `interior`.
    exact interior_maximal hIncl hOpen
  -- Monotonicity of `closure` finishes the proof.
  exact (closure_mono hSub) hx_closure_intA_U

theorem Topology.P2_of_P1_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) (hP1 : Topology.P1 A) : Topology.P2 A := by
  exact ((Topology.P1_iff_P2_of_isOpen (A := A) hA).1) hP1

theorem Topology.interiorClosure_iter2_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First, use idempotence for `closure (interior _ )` with `A := closure A`.
  have h₁ :
      closure (interior (closure (interior (closure (A : Set X))))) =
        closure (interior (closure (A : Set X))) := by
    simpa using
      (Topology.closureInteriorClosureInterior_eq_closureInterior
        (A := closure (A : Set X)))
  -- Apply `interior` to both sides of this equality.
  have h₂ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) :=
    congrArg interior h₁
  -- Use the basic idempotence lemma to simplify the right‐hand side.
  have h₃ :
      interior (closure (interior (closure A))) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (A := A)
  -- Combine the results.
  simpa [h₃] using h₂

theorem Topology.interiorClosure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  -- First, prove `closure A = univ`.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.Subset_univ _
    · intro x _
      -- Since `closure (interior A) = univ`, every point belongs to it.
      have hx_clInt : x ∈ closure (interior A) := by
        have : x ∈ (Set.univ : Set X) := by trivial
        simpa [h] using this
      -- And `closure (interior A) ⊆ closure A`.
      have hIncl : closure (interior A) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior A ⊆ (A : Set X))
      exact hIncl hx_clInt
  -- Taking interiors yields the desired equality.
  simpa [hClosureA, interior_univ]

theorem Topology.interiorClosure_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.interiorClosure_nonempty_of_P3 (A := A) hP3 hA

theorem Topology.closureInteriorClosureClosure_eq_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure (A : Set X))) := by
  simpa [closure_closure]

theorem Topology.P3_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P3 A → IsOpen U → Topology.P3 (A ∩ U) := by
  intro hP3A hUopen
  dsimp [Topology.P3] at hP3A ⊢
  intro x hxAU
  rcases hxAU with ⟨hxA, hxU⟩
  have hxInt : x ∈ interior (closure A) := hP3A hxA
  -- `S` is an open neighbourhood of `x`
  have hOpenS : IsOpen (interior (closure A) ∩ U) :=
    (isOpen_interior).inter hUopen
  have hSubS : (interior (closure A) ∩ U : Set X) ⊆ closure (A ∩ U) := by
    intro y hy
    have hyInt : y ∈ interior (closure A) := hy.1
    have hyU   : y ∈ U := hy.2
    have hyClA : y ∈ closure A := interior_subset hyInt
    -- Show `y ∈ closure (A ∩ U)`
    have hMem : y ∈ closure (A ∩ U) := by
      -- Employ the neighbourhood characterisation of closure
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- Work with the open neighbourhood `V ∩ U` of `y`
      have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- Since `y ∈ closure A`, this neighbourhood meets `A`
      have hNonempty : ((V ∩ U) ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ U) hVUopen hyVU
      -- Re-arrange intersections to obtain the required non-emptiness
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hNonempty
    exact hMem
  have hxS : x ∈ interior (closure A) ∩ U := ⟨hxInt, hxU⟩
  -- Maximality of the interior gives the desired inclusion
  have hIncl : (interior (closure A) ∩ U : Set X) ⊆
      interior (closure (A ∩ U)) :=
    interior_maximal hSubS hOpenS
  exact hIncl hxS

theorem Topology.P2_inter_open {X : Type*} [TopologicalSpace X] {A U : Set X} :
    Topology.P2 A → IsOpen U → Topology.P2 (A ∩ U) := by
  intro hP2A hUopen
  dsimp [Topology.P2] at *
  intro x hxAU
  rcases hxAU with ⟨hxA, hxU⟩
  -- `x` already lies in the interior of the closure of `interior A`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2A hxA
  -- The open set we'll work with.
  set M : Set X := interior (closure (interior A)) ∩ U with hMdef
  have hOpenM : IsOpen M := by
    simpa [hMdef] using (isOpen_interior).inter hUopen
  have hxM : x ∈ M := by
    simpa [hMdef] using And.intro hxInt hxU
  -- Show that `M` is contained in the closure of `interior (A ∩ U)`.
  have hSubM : (M : Set X) ⊆ closure (interior (A ∩ U)) := by
    intro y hyM
    have hyIntA : y ∈ interior (closure (interior A)) := by
      simpa [hMdef] using hyM.1
    have hyU : y ∈ U := by
      simpa [hMdef] using hyM.2
    -- From `hyIntA` we deduce `y ∈ closure (interior A)`.
    have hyClA : y ∈ closure (interior A) := interior_subset hyIntA
    -- We first show `y ∈ closure (interior A ∩ U)`.
    have hClosure1 : y ∈ closure (interior A ∩ U) := by
      -- Use the neighbourhood characterisation of closure.
      apply (mem_closure_iff).2
      intro V hVopen hyV
      -- `V ∩ U` is an open neighbourhood of `y`.
      have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- Since `y ∈ closure (interior A)`, this neighbourhood meets `interior A`.
      have hNonempty : ((V ∩ U) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ U) hVUopen hyVU
      -- Rearrange intersections to fit the goal.
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using hNonempty
    -- `interior A ∩ U` is open and contained in `interior (A ∩ U)`.
    have hIncl : (interior A ∩ U : Set X) ⊆ interior (A ∩ U) := by
      -- Openness.
      have hOpen : IsOpen (interior A ∩ U) := (isOpen_interior).inter hUopen
      -- Containment.
      have hSub : (interior A ∩ U : Set X) ⊆ A ∩ U := by
        intro z hz
        exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
      exact interior_maximal hSub hOpen
    -- Monotonicity of closure turns the previous step into the desired inclusion.
    have hClosureIncl : closure (interior A ∩ U) ⊆ closure (interior (A ∩ U)) :=
      closure_mono hIncl
    exact hClosureIncl hClosure1
  -- Maximality of the interior now yields the result.
  have hFinal :
      (M : Set X) ⊆ interior (closure (interior (A ∩ U))) :=
    interior_maximal hSubM hOpenM
  -- Conclude for our original `x`.
  exact hFinal hxM

theorem Topology.P2_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P2 A := by
  exact ((Topology.P2_iff_P3_of_isClosed (A := A) hA).2) hP3



theorem Topology.P1_P2_P3_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    (Topology.P1 F ∧ Topology.P2 F ∧ Topology.P3 F) ↔ IsOpen F := by
  have hP1 := Topology.P1_finite_iff_isOpen_of_T1 (F := F) hF
  have hP2 := Topology.P2_finite_iff_isOpen_of_T1 (F := F) hF
  have hP3 := Topology.P3_finite_iff_isOpen_of_T1 (F := F) hF
  constructor
  · intro hTriple
    exact (hP1).1 hTriple.1
  · intro hOpen
    exact ⟨(hP1).2 hOpen, (hP2).2 hOpen, (hP3).2 hOpen⟩

theorem Topology.P3_subset_interiorClosure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hP3 : Topology.P3 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxIntA : x ∈ interior (closure A) := hP3 hxA
  have hMono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono (closure_mono hAB)
  exact hMono hxIntA

theorem Topology.P2_iff_P3_of_interiorClosureInterior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure (interior A)) = interior (closure A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  simpa [Topology.P2, Topology.P3, hEq]

theorem Topology.P1_closure_iff_closureInteriorClosure_eq {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  simpa [closure_closure] using
    (Topology.P1_iff_closure_eq_closureInterior
      (A := closure (A : Set X)))

theorem Topology.subset_interiorClosure_of_subset_P2 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  have hxInt : x ∈ interior (closure (interior B)) := hP2B hxB
  have hIncl : interior (closure (interior B)) ⊆ interior (closure B) :=
    interiorClosureInterior_subset_interiorClosure (A := B)
  exact hIncl hxInt

theorem Topology.closureInteriorClosureInteriorClosureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  -- First reduction using the idempotence lemma with `A := closure (interior A)`
  have h1 :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closureInteriorClosureInterior_eq_closureInterior
        (A := closure (interior A)))
  -- Second reduction using the idempotence lemma with the original set `A`
  have h2 :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closureInteriorClosureInterior_eq_closureInterior
        (A := A))
  simpa [h1, h2]

theorem Topology.interiorClosureInterior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_left
      exact hSub hA
  | inr hB =>
      have hSub : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        exact Set.subset_union_right
      exact hSub hB

theorem Topology.interiorClosureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Show membership in `interior (closure (interior A))`.
  have hA : x ∈ interior (closure (interior A)) := by
    have hSub : interior (closure (interior (A ∩ B))) ⊆
        interior (closure (interior A)) := by
      apply interior_mono
      apply closure_mono
      apply interior_mono
      exact Set.inter_subset_left
    exact hSub hx
  -- Show membership in `interior (closure (interior B))`.
  have hB : x ∈ interior (closure (interior B)) := by
    have hSub : interior (closure (interior (A ∩ B))) ⊆
        interior (closure (interior B)) := by
      apply interior_mono
      apply closure_mono
      apply interior_mono
      exact Set.inter_subset_right
    exact hSub hx
  exact ⟨hA, hB⟩

theorem Topology.interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) : (interior A).Nonempty := by
  -- `P2` implies `P1`.
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  -- Use the existing result for `P1`.
  exact Topology.interior_nonempty_of_P1 (A := A) hP1 hA

theorem Topology.P1_P2_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_dense_interior (A := A) h
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) h
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) h
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.closureInteriorClosure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- Since `closure A` is open, its interior is itself.
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  -- Rewrite using this fact and simplify with idempotency of `closure`.
  calc
    closure (interior (closure (A : Set X)))
        = closure (closure (A : Set X)) := by
          simpa [hInt]
    _ = closure (A : Set X) := by
          simpa [closure_closure]

theorem Topology.IsOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  simpa using (Topology.IsOpen_P1_and_P3 (A := A) hA).2

theorem Topology.IsOpen_P1_P2_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    Topology.P1 (closure (A : Set X)) ∧
      Topology.P2 (closure (A : Set X)) ∧
      Topology.P3 (closure (A : Set X)) := by
  simpa using
    (Topology.IsOpen_P1_P2_P3 (A := closure (A : Set X)) hOpen)

theorem Topology.interiorClosure_iter3_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior
      (closure (interior (closure A))))))) = interior (closure A) := by
  have h₁ :=
    Topology.interiorClosure_iter2_idempotent
      (A := interior (closure A))
  have h₂ := Topology.interiorClosure_idempotent (A := A)
  simpa using h₁.trans h₂

theorem Topology.closureInterior_eq_of_P2_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = (A : Set X) := by
  -- From `P2` we immediately obtain `P1`.
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  -- Apply the characterisation of `P1` for closed sets.
  exact (Topology.P1_closed_iff_closureInterior_eq (A := A) hA).1 hP1

theorem Topology.interior_iUnion_of_open {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} (hF : ∀ i, IsOpen (F i)) :
    interior (⋃ i, F i) = ⋃ i, F i := by
  have hOpen : IsOpen (⋃ i, F i) := isOpen_iUnion hF
  simpa using hOpen.interior_eq

theorem Topology.P2_closureInteriorClosure_iff_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure (A : Set X)))) := by
  -- `closure (interior (closure A))` is closed, so we can use the closed‐set characterisation
  -- of `P2`.
  have hClosed : IsClosed (closure (interior (closure (A : Set X)))) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_isOpen
        (A := closure (interior (closure (A : Set X)))) hClosed)

theorem Topology.P1_superset_of_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` belongs to `closure (interior A)` by the hypothesis `hBsubset`.
  have hx_clA : x ∈ closure (interior A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `interior A ⊆ interior B`.
  have hIntSubset : interior A ⊆ interior B := interior_mono hAB
  -- Taking closures preserves inclusion.
  have hClSubset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntSubset
  -- Conclude that `x ∈ closure (interior B)`.
  exact hClSubset hx_clA

theorem Topology.subset_interiorClosureInterior_of_subset_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP2B hxB

theorem Topology.interiorClosureClosureInterior_eq_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (interior (A : Set X)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interiorClosureClosure_eq_interiorClosure (A := interior A))

theorem Topology.interiorClosure_iter4_idempotent {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure A))))))))) =
      interior (closure A) := by
  -- First, use the `iter3` idempotence lemma to simplify the innermost part.
  have h₁ :=
    Topology.interiorClosure_iter3_idempotent (A := A)
  have h₂ :
      interior (closure (interior (closure (interior (closure (interior
        (closure (interior (closure A))))))))) =
        interior (closure (interior (closure A))) := by
    simpa [h₁]
  -- A final application of the basic idempotence lemma finishes the proof.
  calc
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure A))))))))) =
        interior (closure (interior (closure A))) := h₂
    _ = interior (closure A) :=
        Topology.interiorClosure_idempotent (A := A)

theorem Topology.P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hOpen
  have hEquiv := (Topology.P2_closure_iff_isOpen (A := A))
  exact (hEquiv).2 hOpen

theorem Topology.interior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior (closure A))) := by
  intro x hx
  -- Step 1: `x` belongs to `interior (closure A)`.
  have hx₁ : x ∈ interior (closure A) :=
    (Topology.interior_subset_interiorClosure (A := A)) hx
  -- Step 2: use the inclusion for `closure A`.
  have hIncl :
      interior (closure A) ⊆ interior (closure (interior (closure A))) :=
    Topology.interior_subset_interiorClosureInterior (A := closure A)
  exact hIncl hx₁

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hx
  exact subset_closure hx

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  exact (Topology.P1_P2_P3_empty (X := X)).2.1

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  exact (Topology.P1_P2_P3_empty (X := X)).2.2

theorem Topology.P2_iff_P3_singleton_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P2 ({x} : Set X) ↔ Topology.P3 ({x} : Set X) := by
  have hP2 : Topology.P2 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P2_singleton_iff_isOpen_of_T1 (x := x)
  have hP3 : Topology.P3 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P3_singleton_iff_isOpen_of_T1 (x := x)
  simpa using hP2.trans hP3.symm

theorem Topology.P1_iff_P2_singleton_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P1 ({x} : Set X) ↔ Topology.P2 ({x} : Set X) := by
  have h₁ := (Topology.P1_singleton_iff_isOpen_of_T1 (x := x))
  have h₂ := (Topology.P2_singleton_iff_isOpen_of_T1 (x := x))
  simpa using h₁.trans h₂.symm

theorem Topology.P3_superset_of_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  have hxIntA : x ∈ interior (closure A) := hBsubset hxB
  have hIncl : interior (closure A) ⊆ interior (closure B) :=
    interior_mono (closure_mono hAB)
  exact hIncl hxIntA

theorem Topology.interiorClosure_iter5_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure A))))))))) =
      interior (closure A) := by
  -- Apply the 4-fold idempotence lemma to `interior (closure A)`.
  have h :=
    Topology.interiorClosure_iter4_idempotent (A := interior (closure A))
  -- Simplify the right‐hand side using the basic idempotence lemma.
  simpa [Topology.interiorClosure_idempotent (A := A)] using h

theorem Topology.P1_P2_P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · intro hTriple
    rcases hTriple with ⟨_, _, hP3⟩
    exact (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
  · intro hOpen
    exact (Topology.IsOpen_P1_P2_P3 (A := A) hOpen)

theorem Topology.P1_iff_P3_singleton_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P1 ({x} : Set X) ↔ Topology.P3 ({x} : Set X) := by
  have h₁ := (Topology.P1_singleton_iff_isOpen_of_T1 (x := x))
  have h₃ := (Topology.P3_singleton_iff_isOpen_of_T1 (x := x))
  simpa using h₁.trans h₃.symm

theorem Topology.interiorClosureInterior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔
      interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`,
    -- hence it must also be empty.
    have hSub : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ interior (closure (interior A)) :=
        (Topology.interior_subset_interiorClosureInterior (A := A)) hx
      simpa [h] using this
    -- Use `Subset.antisymm` to obtain the desired equality.
    apply Set.Subset.antisymm
    · exact hSub
    · intro x hx
      cases hx
  · intro hInt
    -- From `interior A = ∅` we derive
    -- `closure (interior A) = ∅` and hence its interior is also `∅`.
    have hClosure : closure (interior A) = (∅ : Set X) := by
      simpa [hInt] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))
    simpa [hClosure] using
      (interior_empty : interior (∅ : Set X) = (∅ : Set X))

theorem Topology.P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Equivalences available for open sets
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Establish the two directions of the desired equivalence
  constructor
  · intro hP2
    -- From `P2` obtain `P1`, then `P3`
    have hP1 : Topology.P1 A := hP1P2.mpr hP2
    have hP3 : Topology.P3 A := hP1P3.mp hP1
    exact ⟨hP1, hP3⟩
  · rintro ⟨hP1, _hP3⟩
    -- From `P1` recover `P2`
    exact hP1P2.mp hP1

theorem Topology.P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A ↔ interior (A : Set X) = A := by
  -- First, translate `P2 A` into the openness of `A`.
  have hOpenEquiv : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_isOpen (A := A) hA
  constructor
  · intro hP2
    -- From `P2` we obtain that `A` is open, hence its interior is itself.
    have hOpen : IsOpen A := hOpenEquiv.1 hP2
    simpa using hOpen.interior_eq
  · intro hIntEq
    -- The equality `interior A = A` implies that `A` is open.
    have hOpen : IsOpen A := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
    -- Convert openness back to `P2` via the previously established equivalence.
    exact hOpenEquiv.2 hOpen

theorem Topology.P2_superset_of_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  have hxIntA : x ∈ interior (closure (interior A)) := hBsubset hxB
  have hIncl : interior (closure (interior A)) ⊆
      interior (closure (interior B)) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    exact hAB
  exact hIncl hxIntA

theorem Topology.P3_closureInteriorClosure_iff_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure (A : Set X)))) := by
  have hClosed :
      IsClosed (closure (interior (closure (A : Set X)))) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen
        (A := closure (interior (closure (A : Set X)))) hClosed)

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  exact (Topology.P1_P2_P3_univ (X := X)).2.1

theorem Topology.closureInterior_union_eq_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- The set `A ∪ B` is open, so its interior is itself.
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  have hInt : interior (A ∪ B) = A ∪ B := hOpen.interior_eq
  -- Distribute `closure` over the union.
  simpa [hInt, closure_union]

theorem Topology.closureInterior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) : closure (interior A) = closure A := by
  have hEq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  simpa using hEq.symm

theorem Topology.interiorClosure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty, interior_empty]

theorem Topology.closureInteriorClosure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- We prove the two inclusions separately.
  apply Set.Subset.antisymm
  ·
    exact Topology.closureInteriorClosure_subset_closure (A := A)
  ·
    -- From `P1` we have `closure A = closure (interior A)`.
    have hEq : closure (A : Set X) = closure (interior A) :=
      (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
    -- `interior A ⊆ interior (closure A)` by monotonicity of `interior`.
    have hIncl : closure (interior A) ⊆
        closure (interior (closure (A : Set X))) := by
      apply closure_mono
      exact Topology.interior_subset_interiorClosure (A := A)
    -- Rewrite using the equality obtained from `P1`.
    simpa [hEq] using hIncl

theorem Topology.P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Equivalences already established for open sets
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  -- Prove each direction of the desired equivalence
  constructor
  · intro hP3
    -- From `P3` obtain `P1`
    have hP1 : Topology.P1 A := (hP1P3).mpr hP3
    -- From `P1` obtain `P2`
    have hP2 : Topology.P2 A := (hP1P2).mp hP1
    exact ⟨hP1, hP2⟩
  · rintro ⟨hP1, _hP2⟩
    -- From `P1` recover `P3`
    exact (hP1P3).mp hP1

theorem Topology.closureInterior_nonempty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  exact ⟨x, (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hxInt⟩

theorem Topology.P2_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  exact Topology.P2_of_P3_closed (A := closure (A : Set X)) hClosed hP3

theorem Topology.isOpen_closureInterior_iff_isOpen_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    IsOpen (closure (interior A)) ↔ IsOpen (closure (A : Set X)) := by
  -- From `P2` we know the closures coincide.
  have hEq : closure (interior A) = closure (A : Set X) :=
    Topology.closureInterior_eq_closure_of_P2 (A := A) hP2
  -- Rewriting one side of the equivalence with this equality
  -- turns both sides into the same statement, giving a trivial equivalence.
  simpa [hEq] using
    (Iff.rfl :
      IsOpen (closure (interior A)) ↔ IsOpen (closure (interior A)))

theorem Topology.P2_subset_interiorClosureInterior_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2A : Topology.P2 A) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  -- From `P2 A` we have `x ∈ interior (closure (interior A))`.
  have hxIntA : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Monotonicity under the inclusion `A ⊆ B`.
  have hMonotone :
      interior (closure (interior A)) ⊆ interior (closure (interior B)) :=
    Topology.interiorClosureInterior_mono hAB
  exact hMonotone hxIntA

theorem Topology.closure_eq_closureInteriorClosure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  simpa using
    (Topology.closure_eq_closureInteriorClosure_of_P3 (A := A) hP3)

theorem Topology.isOpen_closure_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure (A : Set X)) = closure (A : Set X) := by
  constructor
  · intro hOpen
    simpa using hOpen.interior_eq
  · intro hEq
    have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using this

theorem Topology.isOpen_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : IsOpen A := by
  exact (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3

theorem Topology.P1_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B →
      Topology.P1 (closure (A : Set X) ∪ closure (B : Set X)) := by
  intro hP1A hP1B
  -- First, upgrade `P1 A` and `P1 B` to their closures.
  have hP1_clA : Topology.P1 (closure (A : Set X)) :=
    Topology.P1_closure_of_P1 (A := A) hP1A
  have hP1_clB : Topology.P1 (closure (B : Set X)) :=
    Topology.P1_closure_of_P1 (A := B) hP1B
  -- Apply the union lemma for `P1`.
  have hUnion :=
    Topology.P1_union (A := closure (A : Set X)) (B := closure (B : Set X))
      hP1_clA hP1_clB
  -- Rewrite the goal in a convenient form.
  simpa using hUnion

theorem Topology.closureInterior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem Topology.interiorClosure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem Topology.closure_eq_univ_of_P2_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A)
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- First, derive `P1 A` from `P2 A`.
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  -- Apply the existing result for `P1`.
  exact Topology.closure_eq_univ_of_P1_dense_interior (A := A) hP1 hDense

theorem Topology.P3_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A ⊆ closure (interior (closure A)) := by
  intro hP3
  -- `P3` yields the inclusion `A ⊆ interior (closure A)`.
  have h₁ : (A : Set X) ⊆ interior (closure A) := hP3
  -- The interior of any set is contained in its closure.
  have h₂ : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro x hx
    exact subset_closure hx
  -- Transitivity of inclusions gives the result.
  exact Set.Subset.trans h₁ h₂

theorem Topology.closureInterior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ (A : Set X) := by
  have h : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior A ⊆ A)
  simpa [hA.closure_eq] using h

theorem Topology.P2_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ closure (interior (closure (interior A))) := by
  intro hP2 x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  exact subset_closure hxInt

theorem Topology.closureInterior_union_eq_closure_union_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) =
      closure (interior A ∪ interior B) := by
  simpa using (closure_union (interior A) (interior B)).symm

theorem Topology.P2_closureInterior_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (closure (interior (A : Set X))) := by
  have hEquiv := (Topology.P2_closureInterior_iff_isOpen (A := A))
  exact (hEquiv).2 hOpen

theorem Topology.isOpen_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  exact (Topology.P2_closed_iff_isOpen (A := A) hA).1 hP2

theorem Topology.P1_iff_P2_finite_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P1 F ↔ Topology.P2 F := by
  have hP1 := Topology.P1_finite_iff_isOpen_of_T1 (F := F) hF
  have hP2 := Topology.P2_finite_iff_isOpen_of_T1 (F := F) hF
  simpa using hP1.trans hP2.symm

theorem Topology.P3_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A ⊆ closure A := by
  intro hP3
  dsimp [Topology.P3] at hP3
  intro x hxA
  have : x ∈ interior (closure A) := hP3 hxA
  exact interior_subset this

theorem Topology.closureInterior_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure (interior A))) := by
  -- First, note the basic inclusion `interior A ⊆ interior (closure (interior A))`.
  have h : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interiorClosureInterior (A := A)
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono h

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  simpa using (Topology.P1_P2_P3_univ (X := X)).1



theorem Topology.P1_P2_P3_singleton_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    (Topology.P1 ({x} : Set X) ∧ Topology.P2 ({x} : Set X) ∧ Topology.P3 ({x} : Set X))
      ↔ IsOpen ({x} : Set X) := by
  have hP1 : Topology.P1 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P1_singleton_iff_isOpen_of_T1 (x := x)
  have hP2 : Topology.P2 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P2_singleton_iff_isOpen_of_T1 (x := x)
  have hP3 : Topology.P3 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P3_singleton_iff_isOpen_of_T1 (x := x)
  constructor
  · intro hTriple
    exact (hP1).1 hTriple.1
  · intro hOpen
    exact ⟨(hP1).2 hOpen, (hP2).2 hOpen, (hP3).2 hOpen⟩

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa using hOpen.interior_eq

theorem interior_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B : Set X) := hA.inter hB
  simpa using hOpen.interior_eq

theorem Topology.P1_P2_P3_of_isClopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hOpen : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact Topology.IsOpen_P1_P2_P3 (A := A) hOpen

theorem Topology.closureInteriorClosureInterior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆ closure (A : Set X) := by
  -- `interior (closure (interior A)) ⊆ closure (interior A)`
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- `closure (interior A) ⊆ closure A`
  have h₂ : (closure (interior A) : Set X) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Combine the two inclusions.
  have h₃ : interior (closure (interior A)) ⊆ closure (A : Set X) :=
    Set.Subset.trans h₁ h₂
  -- Taking closures preserves inclusion.
  have h₄ :
      closure (interior (closure (interior A))) ⊆
        closure (closure (A : Set X)) :=
    closure_mono h₃
  -- Simplify using idempotence of `closure`.
  simpa [closure_closure] using h₄

theorem Topology.P1_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure (interior A))) := by
  intro hP1 x hxA
  -- From `P1` we get membership in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Use the established inclusion
  -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`.
  have hIncl :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    Topology.closureInterior_subset_closureInteriorClosureInterior (A := A)
  exact hIncl hx_cl

theorem Topology.closureInterior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒞 : Set (Set X)} :
    (∀ s, s ∈ 𝒞 → Topology.P1 s) → Topology.P1 (⋃₀ 𝒞) := by
  intro h𝒞
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS_mem, hxS⟩
  -- From `P1 S` we obtain membership in `closure (interior S)`.
  have hx_closureS : x ∈ closure (interior S) := (h𝒞 S hS_mem) hxS
  -- We show that `closure (interior S)` is contained in
  -- `closure (interior (⋃₀ 𝒞))`.
  have hSub : closure (interior S) ⊆ closure (interior (⋃₀ 𝒞)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨S, hS_mem, hy⟩
  exact hSub hx_closureS

theorem Topology.P1_iff_P3_finite_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P1 F ↔ Topology.P3 F := by
  have h₁ : Topology.P1 F ↔ IsOpen F :=
    Topology.P1_finite_iff_isOpen_of_T1 (F := F) hF
  have h₂ : Topology.P3 F ↔ IsOpen F :=
    Topology.P3_finite_iff_isOpen_of_T1 (F := F) hF
  simpa using h₁.trans h₂.symm



theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒞 : Set (Set X)} :
    (∀ s, s ∈ 𝒞 → Topology.P3 s) → Topology.P3 (⋃₀ 𝒞) := by
  intro h𝒞
  dsimp [Topology.P3]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS_mem, hxS⟩
  have hx_int : x ∈ interior (closure S) := h𝒞 S hS_mem hxS
  have hSub : interior (closure S) ⊆ interior (closure (⋃₀ 𝒞)) := by
    apply interior_mono
    have : (closure S : Set X) ⊆ closure (⋃₀ 𝒞) := by
      apply closure_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨S, hS_mem, hy⟩
    exact this
  exact hSub hx_int

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒞 : Set (Set X)} :
    (∀ s, s ∈ 𝒞 → Topology.P2 s) → Topology.P2 (⋃₀ 𝒞) := by
  classical
  intro h𝒞
  dsimp [Topology.P2]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS_mem, hxS⟩
  have hx_int : x ∈ interior (closure (interior S)) := (h𝒞 S hS_mem) hxS
  have hSub : interior (closure (interior S)) ⊆
      interior (closure (interior (⋃₀ 𝒞))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_sUnion.2 ⟨S, hS_mem, hy⟩
  exact hSub hx_int

theorem Topology.P2_of_P3_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) (hP3 : Topology.P3 A) : Topology.P2 A := by
  exact (Topology.P2_iff_P3_of_isOpen (A := A) hA).mpr hP3

theorem Topology.closureInterior_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : closure (interior A) = A := by
  -- First, derive `P1 A` from `P3 A` and the closedness of `A`.
  have hP1 : Topology.P1 A := Topology.P1_of_P3_closed (A := A) hA hP3
  -- Then apply the closed‐set characterisation of `P1`.
  exact (Topology.P1_closed_iff_closureInterior_eq (A := A) hA).1 hP1

theorem Topology.P2_of_dense_interiorClosureInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : interior (closure (interior A)) = (Set.univ : Set X)) :
    Topology.P2 A := by
  simpa [Topology.P2, hA] using (Set.subset_univ (A := A))

theorem Topology.P2_iff_P3_finite_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P2 F ↔ Topology.P3 F := by
  have hP2 : Topology.P2 F ↔ IsOpen F :=
    Topology.P2_finite_iff_isOpen_of_T1 (F := F) hF
  have hP3 : Topology.P3 F ↔ IsOpen F :=
    Topology.P3_finite_iff_isOpen_of_T1 (F := F) hF
  simpa using hP2.trans hP3.symm

theorem Topology.P2_interior_iff_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P2_iff_P3_of_isOpen (A := interior A) hOpen)

theorem Topology.closureInterior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      have : (x : X) ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    · intro x hx
      cases hx
  · intro hInt
    simpa [hInt] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))

theorem Topology.interiorClosure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    interior (closure (⋂ i, F i)) ⊆ ⋂ i, interior (closure (F i)) := by
  intro x hx
  -- We will show that `x` belongs to each component of the intersection.
  have h : ∀ i, x ∈ interior (closure (F i)) := by
    intro i
    -- Use monotonicity of `closure` and `interior` stemming from
    -- the inclusion `⋂ i, F i ⊆ F i`.
    have hSub : interior (closure (⋂ j, F j)) ⊆ interior (closure (F i)) := by
      apply interior_mono
      have h₀ : (⋂ j, F j : Set X) ⊆ F i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact closure_mono h₀
    exact hSub hx
  -- Assemble the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 h

theorem Topology.closureInteriorClosure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (closure (A ∩ B))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- First inclusion toward the `A` component.
  have hA : closure (interior (closure (A ∩ B)))
      ⊆ closure (interior (closure A)) := by
    apply closure_mono
    apply interior_mono
    -- `closure (A ∩ B)` is contained in `closure A`.
    have : (closure (A ∩ B) : Set X) ⊆ closure A := by
      apply closure_mono
      exact Set.inter_subset_left
    exact this
  -- Second inclusion toward the `B` component.
  have hB : closure (interior (closure (A ∩ B)))
      ⊆ closure (interior (closure B)) := by
    apply closure_mono
    apply interior_mono
    -- `closure (A ∩ B)` is contained in `closure B`.
    have : (closure (A ∩ B) : Set X) ⊆ closure B := by
      apply closure_mono
      exact Set.inter_subset_right
    exact this
  exact ⟨hA hx, hB hx⟩

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  simpa using (Topology.P1_P2_P3_univ (X := X)).2.2

theorem Topology.interior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    interior (⋂ i, F i) ⊆ ⋂ i, interior (F i) := by
  intro x hx
  -- For each index `i`, show `x ∈ interior (F i)`.
  have h : ∀ i, x ∈ interior (F i) := by
    intro i
    -- The set `⋂ i, F i` is contained in `F i`.
    have hSub : (⋂ j, F j : Set X) ⊆ F i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` transports the inclusion.
    have hIncl : interior (⋂ j, F j) ⊆ interior (F i) :=
      interior_mono hSub
    exact hIncl hx
  -- Assemble the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 h

theorem Topology.interiorClosureInterior_eq_univ_iff_closureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (Set.univ : Set X) ↔
      closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro h
    -- `interior (closure (interior A))` is contained in `closure (interior A)`.
    have hSub : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    -- Hence `univ ⊆ closure (interior A)`.
    have hIncl : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [h] using hSub
    -- The reverse inclusion is immediate.
    exact Set.Subset.antisymm (Set.Subset_univ _) hIncl
  · intro h
    simpa [h, interior_univ]

theorem Topology.P1_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P1_iff_P2_of_isOpen (A := interior A) hOpen)

theorem Topology.isOpen_of_interiorClosure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = A → IsOpen A := by
  intro hEq
  have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  simpa [hEq] using this

theorem Topology.interior_sUnion_of_open {X : Type*} [TopologicalSpace X]
    {𝒞 : Set (Set X)} (h𝒞 : ∀ s, s ∈ 𝒞 → IsOpen (s : Set X)) :
    interior (⋃₀ 𝒞 : Set X) = ⋃₀ 𝒞 := by
  have hOpen : IsOpen (⋃₀ 𝒞 : Set X) := isOpen_sUnion h𝒞
  simpa using hOpen.interior_eq

theorem Topology.closureInteriorClosureInterior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  -- First, relate the interiors of the two sets.
  have h₁ :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interiorClosureInterior_subset_interiorClosure (A := A)
  -- Next, every set is contained in the closure of itself.
  have h₂ :
      interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  -- Combine the two inclusions.
  have hIncl :
      interior (closure (interior A)) ⊆ closure (interior (closure A)) :=
    Set.Subset.trans h₁ h₂
  -- Taking closures preserves inclusions; simplify the right‐hand side.
  simpa [closure_closure] using closure_mono hIncl

theorem Topology.closureInterior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    closure (interior (⋂ i, F i : Set X)) ⊆ ⋂ i, closure (interior (F i)) := by
  intro x hx
  -- We show that `x` belongs to each component of the intersection.
  have h : ∀ i, x ∈ closure (interior (F i)) := by
    intro i
    -- First, note that `⋂ i, F i ⊆ F i`.
    have hSub₀ : (⋂ j, F j : Set X) ⊆ F i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking interiors preserves inclusion, hence
    -- `interior (⋂ i, F i) ⊆ interior (F i)`.
    have hSub₁ : interior (⋂ j, F j : Set X) ⊆ interior (F i) :=
      interior_mono hSub₀
    -- Taking closures preserves inclusion as well.
    have hSub₂ :
        closure (interior (⋂ j, F j : Set X)) ⊆
          closure (interior (F i)) :=
      closure_mono hSub₁
    exact hSub₂ hx
  -- Assemble the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 h

theorem Topology.P2_interiorClosureClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (closure (A : Set X)))) := by
  simpa [closure_closure] using
    (Topology.P2_interiorClosure (A := closure (A : Set X)))

theorem Topology.closureInterior_eq_of_P1_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP1 : Topology.P1 A) : closure (interior A) = (A : Set X) := by
  exact (Topology.P1_closed_iff_closureInterior_eq (A := A) hA).1 hP1

theorem Topology.interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A := by
    exact interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A) hx
  have hxB : x ∈ interior B := by
    exact interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B) hx
  exact ⟨hxA, hxB⟩

theorem Topology.closureInterior_nonempty_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hA : A.Nonempty) :
    (closure (interior A)).Nonempty := by
  -- From `P1` and non-emptiness of `A`, obtain a point in `interior A`.
  have hInt : (interior A).Nonempty :=
    Topology.interior_nonempty_of_P1 (A := A) hP1 hA
  -- Any such point also belongs to `closure (interior A)`.
  rcases hInt with ⟨x, hxInt⟩
  exact ⟨x, subset_closure hxInt⟩

theorem Topology.interiors_union_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : interior A ⊆ interior (A ∪ B) :=
        interior_mono Set.subset_union_left
      exact hSub hA
  | inr hB =>
      have hSub : interior B ⊆ interior (A ∪ B) :=
        interior_mono Set.subset_union_right
      exact hSub hB

theorem Topology.P1_interior_iff_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P1_iff_P3_of_isOpen (A := interior A) hOpen)

theorem Topology.interiorClosure_iter6_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior (closure A))))))))))) =
      interior (closure A) := by
  -- Apply the 5-fold idempotence lemma.
  have h₁ :
      interior (closure (interior (closure (interior (closure (interior
        (closure (interior (closure A))))))))) = interior (closure A) :=
    Topology.interiorClosure_iter5_idempotent (A := A)
  -- Substitute `h₁` and finish with the basic idempotence lemma.
  have :
      interior (closure (interior (closure (interior (closure (interior
        (closure (interior (closure (interior (closure A))))))))))) =
        interior (closure (interior (closure A))) := by
    simpa [h₁]
  simpa [Topology.interiorClosure_idempotent (A := A)] using this

theorem Topology.P2_closure_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure (A : Set X) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_interior_eq (A := closure (A : Set X)) hClosed)

theorem Topology.closure_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  have hA : x ∈ closure (A : Set X) := by
    -- `A ∩ B` is contained in `A`, so the closure of `A ∩ B` is contained in the closure of `A`.
    exact (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hB : x ∈ closure (B : Set X) := by
    -- `A ∩ B` is contained in `B`, hence the closure of `A ∩ B` is contained in the closure of `B`.
    exact (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hA, hB⟩

theorem Topology.P2_P3_closure_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P2 (closure (A : Set X)) ∧ Topology.P3 (closure (A : Set X))) ↔
      IsOpen (closure (A : Set X)) := by
  have hP2 := (Topology.P2_closure_iff_isOpen (A := A))
  have hP3 := (Topology.P3_closure_iff_isOpen (A := A))
  constructor
  · intro h
    exact (hP2).1 h.1
  · intro hOpen
    exact ⟨(hP2).2 hOpen, (hP3).2 hOpen⟩

theorem Topology.P1_P2_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.IsOpen_P1_P2_P3 (A := interior A) hOpen

theorem Topology.P2_iff_P1_and_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- `P2 A` and `P3 A` are each equivalent to `IsOpen A` for closed `A`.
  have hP2Open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_isOpen (A := A) hA
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  constructor
  · intro hP2
    -- From `P2` obtain openness, hence `P1` and `P3`.
    have hOpen : IsOpen A := (hP2Open).1 hP2
    have hP1 : Topology.P1 A := Topology.IsOpen_P1 (A := A) hOpen
    have hP3 : Topology.P3 A := (hP3Open).2 hOpen
    exact ⟨hP1, hP3⟩
  · rintro ⟨_, hP3⟩
    -- From `P3` recover openness, hence `P2`.
    have hOpen : IsOpen A := (hP3Open).1 hP3
    exact (hP2Open).2 hOpen

theorem Topology.P1_and_P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A) ↔ IsOpen A := by
  constructor
  · intro h
    exact
      (Topology.P2_closed_iff_isOpen (A := A) hA).1 h.2
  · intro hOpen
    exact ⟨Topology.IsOpen_P1 (A := A) hOpen, IsOpen_P2 (A := A) hOpen⟩

theorem Topology.subset_interior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : A ⊆ interior A := by
  simpa [hA.interior_eq]

theorem Topology.P1_and_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · intro h
    exact
      (Topology.P3_closed_iff_isOpen (A := A) hA).1 h.2
  · intro hOpen
    exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen)

theorem Topology.interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  exact interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

theorem Topology.closureInterior_iUnion_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (⋃ i, closure (interior (F i))) ⊆ closure (interior (⋃ i, F i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `interior (F i)` is contained in `⋃ i, F i`,
  -- hence its closure is contained in the closure of the interior of that union.
  have hSub :
      closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hx_i

theorem Topology.P1_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  -- `closure A` is closed.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- From `P3` and closedness we obtain that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) :=
    (Topology.P3_closed_iff_isOpen (A := closure (A : Set X)) hClosed).1 hP3
  -- An open set satisfies `P1`.
  exact Topology.IsOpen_P1 (A := closure (A : Set X)) hOpen

theorem Topology.P3_of_P1_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    Topology.P1 A → Topology.P3 A := by
  intro hP1
  have hEquiv := (Topology.P1_iff_P3_of_isOpen (A := A) hOpen)
  exact hEquiv.1 hP1

theorem Topology.P1_P2_P3_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) ∧
      Topology.P2 (interior (closure A)) ∧
      Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.IsOpen_P1_P2_P3 (A := interior (closure A)) hOpen

theorem Topology.P3_subset_interiorClosureInteriorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A ⊆ interior (closure (interior (closure A))) := by
  intro hP3 x hxA
  -- From `P3` we have that `x` belongs to `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- `interior (closure A)` is contained in `interior (closure (interior (closure A)))`.
  have hIncl :
      interior (closure A) ⊆
        interior (closure (interior (closure A))) :=
    Topology.interior_subset_interiorClosureInterior (A := closure A)
  exact hIncl hxInt

theorem Topology.P1_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP2cl
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  exact Topology.P1_of_P2_closed (A := closure (A : Set X)) hClosed hP2cl

theorem Topology.interiorClosure_union_eq_union_of_open_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure (B : Set X))) :
    interior (closure (A ∪ B : Set X)) =
      closure (A : Set X) ∪ closure (B : Set X) := by
  apply Set.Subset.antisymm
  · -- `⊆`: every point in the interior of the closure of `A ∪ B`
    --       belongs to `closure A ∪ closure B`.
    intro x hx
    have : (x : X) ∈ closure (A ∪ B : Set X) := interior_subset hx
    simpa [closure_union] using this
  · -- `⊇`: each point in `closure A ∪ closure B`
    --       lies in the interior of the closure of `A ∪ B`.
    intro x hx
    cases hx with
    | inl hxA =>
        -- Handle the case `x ∈ closure A`.
        have hSub : (closure (A : Set X)) ⊆ closure (A ∪ B : Set X) := by
          apply closure_mono
          exact Set.subset_union_left
        have hIncl :
            closure (A : Set X) ⊆ interior (closure (A ∪ B : Set X)) :=
          interior_maximal hSub hA
        exact hIncl hxA
    | inr hxB =>
        -- Handle the case `x ∈ closure B`.
        have hSub : (closure (B : Set X)) ⊆ closure (A ∪ B : Set X) := by
          apply closure_mono
          exact Set.subset_union_right
        have hIncl :
            closure (B : Set X) ⊆ interior (closure (A ∪ B : Set X)) :=
          interior_maximal hSub hB
        exact hIncl hxB

theorem Topology.closure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure (A : Set X) := by
  exact closure_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    (⋃ i, interior (F i)) ⊆ interior (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hSub : interior (F i) ⊆ interior (⋃ j, F j) := by
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hSub hxFi

theorem Topology.P3_iff_P1_and_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- `P3 A` and `P2 A` are each equivalent to `IsOpen A` whenever `A` is closed.
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_closed_iff_isOpen (A := A) hA
  have hP2Open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_isOpen (A := A) hA
  constructor
  · intro hP3
    -- From `P3` obtain openness, then derive `P1` and `P2`.
    have hOpen : IsOpen A := (hP3Open).1 hP3
    have hP1 : Topology.P1 A := Topology.IsOpen_P1 (A := A) hOpen
    have hP2 : Topology.P2 A := (IsOpen_P2 (A := A) hOpen)
    exact ⟨hP1, hP2⟩
  · rintro ⟨_, hP2⟩
    -- From `P2` recover openness, then obtain `P3`.
    have hOpen : IsOpen A := (hP2Open).1 hP2
    exact (hP3Open).2 hOpen

theorem Topology.P3_of_interiorClosure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = closure (A : Set X)) :
    Topology.P3 A := by
  -- The given equality shows that `closure A` is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [h] using this
  -- Apply the existing result that openness of `closure A` implies `P3 A`.
  exact Topology.P3_of_open_closure (A := A) hOpen

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = interior A ∩ B := by
  ext x
  constructor
  · intro hx
    -- From `x ∈ interior (A ∩ B)` we get `x ∈ interior A`.
    have hxIntA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    -- And `x ∈ B` because the interior is contained in the set itself.
    have hxB : x ∈ B := ((interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx).2
    exact ⟨hxIntA, hxB⟩
  · intro hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- The open set we will use in the maximality argument.
    have hOpen : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    -- This open set is contained in `A ∩ B`.
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    -- Hence it is contained in the interior of `A ∩ B`.
    have hIncl : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal hSub hOpen
    -- Since `x ∈ interior A ∩ B`, we obtain `x ∈ interior (A ∩ B)`.
    exact hIncl ⟨hxIntA, hxB⟩

theorem Topology.interiorClosureInterior_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (Set.univ : Set X))) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]

theorem Topology.interiorClosureInterior_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (∅ : Set X))) = (∅ : Set X) := by
  simp

theorem Topology.interiorClosure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    (⋃ i, interior (closure (F i))) ⊆ interior (closure (⋃ i, F i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hSub : interior (closure (F i)) ⊆ interior (closure (⋃ j, F j)) := by
    apply interior_mono
    have : (closure (F i) : Set X) ⊆ closure (⋃ j, F j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hSub hxFi

theorem Topology.P3_iff_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ A ⊆ interior (closure A) := by
  rfl

theorem Topology.open_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  simpa using interior_maximal subset_closure hA



theorem Topology.eq_empty_of_closure_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = (∅ : Set X)) : A = (∅ : Set X) := by
  -- We show the two inclusions to obtain the desired set equality.
  apply Set.Subset.antisymm
  · -- `A ⊆ ∅`
    intro x hxA
    -- Every element of `A` lies in `closure A`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    -- Rewrite using `h : closure A = ∅`.
    simpa [h] using hx_closure
  · -- `∅ ⊆ A` is trivial.
    intro x hxEmpty
    exact False.elim hxEmpty

theorem Topology.P2_iff_subset_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔ A ⊆ interior (closure (interior A)) := by
  rfl

theorem Topology.interiorClosure_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure (A : Set X)) := by
  -- `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Taking closures preserves this inclusion.
  have hCl : closure (A \ B : Set X) ⊆ closure (A : Set X) := closure_mono hSub
  -- Applying monotonicity of `interior` gives the desired result.
  exact interior_mono hCl

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  ext x
  constructor
  · intro hx
    -- `x` lies in `A`.
    have hxA : (x : X) ∈ A :=
      ((interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx).1
    -- `x` lies in `interior B`.
    have hxIntB : x ∈ interior B := by
      have hSub : interior (A ∩ B : Set X) ⊆ interior B :=
        interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
      exact hSub hx
    exact ⟨hxA, hxIntB⟩
  · intro hx
    rcases hx with ⟨hxA, hxIntB⟩
    -- The open set used for the maximality argument.
    have hOpen : IsOpen (A ∩ interior B) :=
      hA.inter isOpen_interior
    -- `A ∩ interior B` is contained in `A ∩ B`.
    have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨hy.1, (interior_subset : interior B ⊆ B) hy.2⟩
    -- Hence it is contained in the interior of `A ∩ B`.
    have hIncl : (A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal hSub hOpen
    exact hIncl ⟨hxA, hxIntB⟩

theorem Topology.closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort _} (F : ι → Set X) :
    closure (⋂ i, F i : Set X) ⊆ ⋂ i, closure (F i) := by
  intro x hx
  have h : ∀ i, x ∈ closure (F i) := by
    intro i
    have hSub : (⋂ j, F j : Set X) ⊆ F i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    exact (closure_mono hSub) hx
  exact Set.mem_iInter.2 h

theorem Topology.closureInteriorClosureInterior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure (interior B))) := by
  exact
    closure_mono
      (interior_mono
        (closure_mono
          (interior_mono hAB)))

theorem Topology.closure_union_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B : Set X) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B : Set X) := hA.union hB
  simpa using hClosed.closure_eq

theorem Topology.P2_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    A ⊆ interior (closure (interior (closure A))) := by
  intro x hxA
  -- From `P2` we have membership in `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Monotonicity upgrades this to the desired larger set.
  have hMono :
      interior (closure (interior A)) ⊆
        interior (closure (interior (closure A))) := by
    apply interior_mono
    -- Show the corresponding inclusion for the closures.
    have hSub :
        closure (interior A) ⊆ closure (interior (closure A)) := by
      apply closure_mono
      exact Topology.interior_subset_interiorClosure (A := A)
    exact hSub
  exact hMono hxInt

theorem Topology.P1_P2_P3_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) ∧
      Topology.P2 (interior (closure (interior A))) ∧
      Topology.P3 (interior (closure (interior A))) := by
  have hOpen : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.IsOpen_P1_P2_P3 (A := interior (closure (interior A))) hOpen

theorem Topology.P3_interiorClosureClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (closure (A : Set X)))) := by
  simpa [closure_closure] using
    (Topology.P3_interiorClosure (A := A))

theorem Topology.P1_P2_P3_closure_iff_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 (closure (A : Set X)) ∧ Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X))) ↔
      IsOpen (closure (A : Set X)) := by
  -- We already have an equivalence for the pair `P2 ∧ P3`.
  have hPair :=
    (Topology.P2_P3_closure_iff_isOpen (A := A))
  constructor
  · -- From the triple of properties we deduce openness via the pair equivalence.
    intro hTriple
    exact hPair.1 ⟨hTriple.2.1, hTriple.2.2⟩
  · -- Openness immediately gives all three properties.
    intro hOpen
    exact Topology.IsOpen_P1_P2_P3_closure (A := A) hOpen

theorem Topology.P2_iff_P3_of_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) ↔ Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using (Topology.P2_iff_P3_of_isOpen (A := interior (closure A)) hOpen)

theorem Topology.closureInterior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior (A : Set X)) := by
  exact
    closure_mono
      (interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ (A : Set X)))

theorem Topology.interior_iUnion_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    interior (⋃ i, interior (F i) : Set X) = ⋃ i, interior (F i) := by
  -- The union of the interiors is open, hence its interior is itself.
  have hOpen : IsOpen (⋃ i, interior (F i) : Set X) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  simpa [hOpen.interior_eq]

theorem Topology.closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    (⋃ i, closure (F i) : Set X) ⊆ closure (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hIncl : closure (F i) ⊆ closure (⋃ j, F j) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion_of_mem i hy
  exact hIncl hxFi

theorem Topology.eq_empty_of_P3_and_interiorClosure_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A)
    (hInt : interior (closure (A : Set X)) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  classical
  by_cases hA : (A : Set X).Nonempty
  · -- `A` is nonempty: derive a contradiction with `hInt`.
    have hIntNe : (interior (closure (A : Set X))).Nonempty :=
      Topology.interiorClosure_nonempty_of_P3 (A := A) hP3 hA
    rcases hIntNe with ⟨x, hxInt⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hInt] using hxInt
    cases this
  · -- `A` is empty, as desired.
    simpa [Set.not_nonempty_iff_eq_empty] using hA

theorem Topology.IsOpen_P1_P2_P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  simpa using (Topology.IsOpen_P1_P2_P3 (A := A ∪ B) hOpen)

theorem Topology.P3_of_P2_closure_alt {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2cl
  -- `closure A` is closed.
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- From `P2 (closure A)` and closedness we deduce that `closure A` is open.
  have hOpenClosure : IsOpen (closure (A : Set X)) :=
    (Topology.P2_closed_iff_isOpen (A := closure (A : Set X)) hClosed).1 hP2cl
  -- Openness of `closure A` gives `P3 (closure A)`.
  have hP3Closure : Topology.P3 (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen (A := A)).2 hOpenClosure
  -- `P3` transfers from `closure A` to `A` itself.
  exact Topology.P3_of_P3_closure (A := A) hP3Closure

theorem Topology.isOpen_closureInterior_iff_isOpen_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    IsOpen (closure (interior A)) ↔ IsOpen (closure (A : Set X)) := by
  -- From `P1` we have `closure A = closure (interior A)`.
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  constructor
  · intro hOpen
    simpa [hEq] using hOpen
  · intro hOpen
    simpa [hEq] using hOpen

theorem Topology.P3_of_P2_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) (hP2 : Topology.P2 A) : Topology.P3 A := by
  exact (Topology.P2_iff_P3_of_isOpen (A := A) hOpen).1 hP2

theorem Topology.interiorClosure_iter7_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior (closure A))))))))))) =
      interior (closure A) := by
  -- First, reduce the innermost six-fold nest.
  have h₁ :=
    Topology.interiorClosure_iter6_idempotent (A := A)
  -- Apply one more `interior ∘ closure` pair to both sides of `h₁`.
  have h₂ :
      interior (closure (interior (closure
        (interior (closure (interior (closure (interior
          (closure (interior (closure A))))))))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      congrArg (fun S : Set X =>
        interior (closure (interior (closure S)))) h₁
  -- A final use of the basic idempotence lemma completes the proof.
  have h₃ :
      interior (closure (interior (closure A))) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (A := A)
  simpa [h₃] using h₂

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- We prove both inclusions separately.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ univ` is trivial.
    exact Set.Subset_univ _
  · -- To show `univ ⊆ closure A`, start with an arbitrary point `x`.
    intro x _
    -- Using the hypothesis `h`, we have `x ∈ closure (interior A)`.
    have hx_closureInt : x ∈ closure (interior A) := by
      have : x ∈ (Set.univ : Set X) := by
        simp
      simpa [h] using this
    -- Since `interior A ⊆ A`, taking closures gives the required inclusion.
    have hIncl : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact hIncl hx_closureInt

theorem Topology.P2_inter_open_left {X : Type*} [TopologicalSpace X] {A U : Set X} :
    IsOpen A → Topology.P2 U → Topology.P2 (A ∩ U) := by
  intro hOpenA hP2U
  have h := Topology.P2_inter_open (A := U) (U := A) hP2U hOpenA
  simpa [Set.inter_comm] using h

theorem Topology.interior_subset_closure_of_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ⊆ closure (interior A) := by
  intro x hx
  exact subset_closure hx

theorem Topology.P3_of_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P2 A → Topology.P3 A := by
  intro _ hP2
  exact Topology.P2_implies_P3 (A := A) hP2

theorem Topology.eq_empty_of_P1_and_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior A = (∅ : Set X) → A = (∅ : Set X) := by
  classical
  intro hP1 hIntEmpty
  by_cases hA : (A : Set X).Nonempty
  · -- If `A` is non-empty, `P1` yields a contradiction with `interior A = ∅`.
    have hIntNonempty : (interior A).Nonempty :=
      Topology.interior_nonempty_of_P1 (A := A) hP1 hA
    rcases hIntNonempty with ⟨x, hx⟩
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hIntEmpty] using hx
    exact (by cases this)
  · -- Otherwise `A` is empty, as desired.
    simpa [Set.not_nonempty_iff_eq_empty] using hA

theorem Topology.P3_interior_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) ↔ IsOpen (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  have hP3 : Topology.P3 (interior A) := Topology.P3_interior (A := A)
  exact ⟨fun _ => hOpen, fun _ => hP3⟩

theorem Topology.closure_iUnionInterior_subset_closureInterior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    closure (⋃ i, interior (F i) : Set X) ⊆
      closure (interior (⋃ i, F i)) := by
  -- First show that the union of the interiors is contained in the interior of the union.
  have hSub : (⋃ i, interior (F i) : Set X) ⊆ interior (⋃ i, F i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
    -- Monotonicity of `interior` for the inclusion `F i ⊆ ⋃ i, F i`.
    have hIncl : (interior (F i) : Set X) ⊆ interior (⋃ j, F j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    exact hIncl hxFi
  -- Taking closures preserves inclusions.
  exact closure_mono hSub

theorem Topology.P3_union_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 C →
      Topology.P3 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First combine `A` and `B`
  have hAB : Topology.P3 (A ∪ B) := Topology.P3_union hA hB
  -- Then unite the result with `C`
  have hABC : Topology.P3 ((A ∪ B) ∪ C) := Topology.P3_union hAB hC
  -- Reassociate unions to match the desired form
  simpa [Set.union_assoc] using hABC

theorem Topology.P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, combine `A` and `B`.
  have hAB : Topology.P1 (A ∪ B) := Topology.P1_union (A := A) (B := B) hA hB
  -- Then, unite the result with `C`.
  have hABC : Topology.P1 ((A ∪ B) ∪ C) :=
    Topology.P1_union (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the desired form.
  simpa [Set.union_assoc] using hABC

theorem Topology.P1_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P1 (closure (A : Set X)) := by
  have hTriple := Topology.IsOpen_P1_P2_P3_closure (A := A) hOpen
  exact hTriple.1

theorem Topology.P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, unite `A` and `B`.
  have hAB : Topology.P2 (A ∪ B) := Topology.P2_union (A := A) (B := B) hA hB
  -- Then unite the result with `C`.
  have hABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (A := A ∪ B) (B := C) hAB hC
  -- Reassociate unions to match the desired form.
  simpa [Set.union_assoc] using hABC

theorem Topology.P1_closure_of_dense_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h : closure (interior (closure (A : Set X))) = (Set.univ : Set X)) :
    Topology.P1 (closure (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure (interior (closure (A : Set X))) := by
    -- Since this set is the whole space, every point belongs to it.
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [h] using this
  simpa [closure_closure] using this

theorem Topology.P3_inter_open_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) :
    Topology.P3 (A ∩ B ∩ C : Set X) := by
  -- `A` is open, hence satisfies `P3`.
  have hP3A : Topology.P3 (A : Set X) :=
    (Topology.IsOpen_P1_and_P3 (A := A) hA).2
  -- Intersect `A` with the open set `B`.
  have hP3AB : Topology.P3 (A ∩ B : Set X) :=
    Topology.P3_inter_open (A := A) (U := B) hP3A hB
  -- Intersect the result with the open set `C`.
  have hP3ABC : Topology.P3 ((A ∩ B) ∩ C : Set X) :=
    Topology.P3_inter_open (A := A ∩ B) (U := C) hP3AB hC
  -- Reassociate intersections to match the statement.
  simpa [Set.inter_assoc] using hP3ABC

theorem Topology.P3_iff_isOpen_of_closure_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hcl : closure (A : Set X) = A) :
    Topology.P3 A ↔ IsOpen A := by
  -- First, note that `A` is closed because it is equal to its closure.
  have hClosed : IsClosed (A : Set X) := by
    simpa [hcl] using (isClosed_closure : IsClosed (closure (A : Set X)))
  -- Apply the characterisation for closed sets.
  simpa using (Topology.P3_closed_iff_isOpen (A := A) hClosed)

theorem Topology.closure_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B : Set X) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B : Set X) := hA.inter hB
  simpa using hClosed.closure_eq

theorem Topology.interiorClosureInterior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  simpa using
    (Topology.interiorClosureInterior_mono
      (A := A) (B := closure A) (subset_closure : (A : Set X) ⊆ closure A))

theorem Topology.interiorClosure_union_eq_union_interiorClosures
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure (B : Set X))) :
    interior (closure (A ∪ B : Set X)) =
      interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) := by
  -- Start from the existing equality expressed with closures.
  have h :=
    Topology.interiorClosure_union_eq_union_of_open_closures
      (A := A) (B := B) hA hB
  -- Rewrite the right‐hand side using `interior_eq` for the open closures.
  simpa [hA.interior_eq, hB.interior_eq] using h

theorem Topology.interiorClosure_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ⊆
      closure (interior (closure (interior (closure (A : Set X))))) := by
  intro x hx
  -- First, place `x` inside `interior (closure (interior (closure A)))`
  -- using the established inclusion for `A := closure A`.
  have hxInt :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    (Topology.interior_subset_interiorClosureInterior
        (A := closure (A : Set X))) hx
  -- The interior is always contained in the closure of itself.
  exact subset_closure hxInt

theorem Topology.closureInterior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior A) ∪ closure (interior B) ∪ closure (interior C) ⊆
      closure (interior (A ∪ B ∪ C)) := by
  intro x hx
  -- `closure (interior A)` is contained in the target.
  have hAincl : closure (interior A) ⊆ closure (interior (A ∪ B ∪ C)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Or.inl (Or.inl hy)
  -- `closure (interior B)` is contained in the target.
  have hBincl : closure (interior B) ⊆ closure (interior (A ∪ B ∪ C)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Or.inl (Or.inr hy)
  -- `closure (interior C)` is contained in the target.
  have hCincl : closure (interior C) ⊆ closure (interior (A ∪ B ∪ C)) := by
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Or.inr hy
  -- Analyse the membership of `x`.
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA => exact hAincl hA
      | inr hB => exact hBincl hB
  | inr hC => exact hCincl hC

theorem Topology.interiorClosure_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure A) ∪ interior (closure B) ∪ interior (closure C) ⊆
      interior (closure (A ∪ B ∪ C)) := by
  intro x hx
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA =>
          have hSub : interior (closure A) ⊆ interior (closure (A ∪ B ∪ C)) := by
            apply interior_mono
            apply closure_mono
            intro y hy
            exact Or.inl (Or.inl hy)
          exact hSub hA
      | inr hB =>
          have hSub : interior (closure B) ⊆ interior (closure (A ∪ B ∪ C)) := by
            apply interior_mono
            apply closure_mono
            intro y hy
            exact Or.inl (Or.inr hy)
          exact hSub hB
  | inr hC =>
      have hSub : interior (closure C) ⊆ interior (closure (A ∪ B ∪ C)) := by
        apply interior_mono
        apply closure_mono
        intro y hy
        exact Or.inr hy
      exact hSub hC

theorem Topology.closureInterior_iter5_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  simpa [Topology.closureInteriorClosureInterior_eq_closureInterior] using
    (by
      simp [Topology.closureInteriorClosureInterior_eq_closureInterior])

theorem Topology.P1_P2_P3_of_dense_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure (interior A)) = (Set.univ : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interiorClosureInterior (A := A) h
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (A := A) hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (A := A) hP2
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.closureInterior_iter3_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  -- Apply the basic two-step idempotence lemma with `A := interior A`.
  have h :=
    Topology.closureInteriorClosureInterior_eq_closureInterior
      (A := interior A)
  -- Simplify the right-hand side using `interior_interior`.
  simpa [interior_interior] using h

theorem Topology.P2_subset_interiorClosure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2A : Topology.P2 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- From `P2 A` we know `x ∈ interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Step 1: `interior (closure (interior A)) ⊆ interior (closure A)`.
  have hStep1 :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interiorClosureInterior_subset_interiorClosure (A := A)
  -- Step 2: monotonicity under `A ⊆ B`.
  have hStep2 :
      interior (closure A) ⊆ interior (closure B) :=
    interior_mono (closure_mono hAB)
  -- Chain the inclusions to place `x` in `interior (closure B)`.
  exact hStep2 (hStep1 hx₁)

theorem Topology.interiorClosure_union_eq_interiorClosure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : (B : Set X) ⊆ interior (closure (A : Set X))) :
    interior (closure (A ∪ B : Set X)) = interior (closure (A : Set X)) := by
  apply Set.Subset.antisymm
  · -- `⊆` : from left to right
    -- First, show `A ∪ B ⊆ closure A`.
    have hAB : (A ∪ B : Set X) ⊆ closure (A : Set X) := by
      intro x hx
      cases hx with
      | inl hxA =>
          exact subset_closure hxA
      | inr hxB =>
          have : x ∈ interior (closure (A : Set X)) := hB hxB
          exact interior_subset this
    -- Taking closures preserves this inclusion.
    have hCl : closure (A ∪ B : Set X) ⊆ closure (A : Set X) := by
      have h := closure_mono hAB
      simpa [closure_closure] using h
    -- Applying `interior` yields the desired inclusion.
    exact interior_mono hCl
  · -- `⊇` : from right to left
    -- `A ⊆ A ∪ B`, hence `closure A ⊆ closure (A ∪ B)`.
    have hCl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) :=
      closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
    -- Monotonicity of `interior` gives the required inclusion.
    exact interior_mono hCl



theorem Topology.P3_inter_three_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) :
    Topology.P3 A → Topology.P3 B → Topology.P3 C →
    Topology.P3 (A ∩ B ∩ C) := by
  intro hP3A hP3B hP3C
  -- Convert `P3` on closed sets to openness.
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_isOpen (A := B) hB).1 hP3B
  have hOpenC : IsOpen C :=
    (Topology.P3_closed_iff_isOpen (A := C) hC).1 hP3C
  -- The intersection of the three open sets is open.
  have hOpenABC : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
    exact hAB.inter hOpenC
  -- The same intersection is closed as an intersection of closed sets.
  have hClosedABC : IsClosed (A ∩ B ∩ C) := by
    have hAB : IsClosed (A ∩ B) := hA.inter hB
    exact hAB.inter hC
  -- Use the closed-set characterisation `P3 ↔ IsOpen` to obtain `P3`.
  exact
    (Topology.P3_closed_iff_isOpen (A := A ∩ B ∩ C) hClosedABC).2 hOpenABC

theorem Topology.isClosed_closureInterior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (A : Set X))))

theorem Topology.P3_inter_open_left {X : Type*} [TopologicalSpace X] {U A : Set X} :
    IsOpen U → Topology.P3 A → Topology.P3 (U ∩ A) := by
  intro hOpenU hP3A
  have h := Topology.P3_inter_open (A := A) (U := U) hP3A hOpenU
  simpa [Set.inter_comm] using h

theorem Topology.interiorClosure_union_interior_eq_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A ∪ interior A : Set X)) =
      interior (closure (A : Set X)) := by
  -- We apply the more general lemma with `B = interior A`.
  refine
    Topology.interiorClosure_union_eq_interiorClosure
      (A := A) (B := interior A) ?_
  -- Verify the required subset condition.
  intro x hx
  exact
    (Topology.interior_subset_interiorClosure (A := A)) hx

theorem Topology.IsOpen_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (interior (closure (A : Set X))) := by
  simpa using isOpen_interior

theorem Topology.interiorClosure_inter_interSubset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure A) := by
  -- We start with the basic inclusion `A ∩ interior B ⊆ A`.
  have h₀ : (A ∩ interior B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions, giving
  -- `closure (A ∩ interior B) ⊆ closure A`.
  have h₁ : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono h₀
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono h₁

theorem interior_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∪ B ∪ C : Set X) = A ∪ B ∪ C := by
  -- The union of three open sets is open.
  have hOpen : IsOpen (A ∪ B ∪ C : Set X) := by
    have hAB : IsOpen (A ∪ B : Set X) := hA.union hB
    exact hAB.union hC
  -- The interior of an open set is the set itself.
  simpa using hOpen.interior_eq

theorem Topology.P1_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (A : Set X)) : Topology.P1 A := by
  -- The given equality shows that `A` is open.
  have hOpen : IsOpen A := by
    have : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using this
  -- Every open set satisfies `P1`.
  exact Topology.IsOpen_P1 (A := A) hOpen

theorem Topology.P2_inter_three_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) :
    Topology.P2 A → Topology.P2 B → Topology.P2 C →
    Topology.P2 (A ∩ B ∩ C) := by
  intro hP2A hP2B hP2C
  -- Turn the `P2` hypotheses on the three closed sets into openness.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (A := A) hA).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_isOpen (A := B) hB).1 hP2B
  have hOpenC : IsOpen C :=
    (Topology.P2_closed_iff_isOpen (A := C) hC).1 hP2C
  -- The triple intersection of the open sets is itself open.
  have hOpenABC : IsOpen (A ∩ B ∩ C) := by
    have hOpenAB : IsOpen (A ∩ B) := hOpenA.inter hOpenB
    exact hOpenAB.inter hOpenC
  -- An open set satisfies `P2`.
  exact IsOpen_P2 (A := A ∩ B ∩ C) hOpenABC



theorem Topology.P2_of_P1_open_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    Topology.P2 A := by
  dsimp [Topology.P2] at *
  intro x hxA
  -- From `P1` we have `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Because `closure (interior A)` is open, its interior is itself.
  have hEq : interior (closure (interior A)) = closure (interior A) :=
    hOpen.interior_eq
  -- Rewrite and conclude.
  simpa [hEq] using hx_cl

theorem Topology.closureInteriorClosure_eq_closureInterior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  simpa [hA.closure_eq]

theorem Topology.interiorClosureInterior_eq_closureInterior_of_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior A))) :
    interior (closure (interior A)) = closure (interior A) := by
  simpa using hOpen.interior_eq

theorem Topology.P2_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ interior (closure A) := by
  intro hP2
  exact (Topology.P2_implies_P3 (A := A) hP2)

theorem Topology.interiorClosureInterior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure (interior A)) ∪
        interior (closure (interior B)) ∪
        interior (closure (interior C)) ⊆
      interior (closure (interior (A ∪ B ∪ C))) := by
  intro x hx
  -- Split the membership in the three‐fold union
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA =>
          -- Handle the case `x ∈ interior (closure (interior A))`
          have hSub :
              interior (closure (interior A)) ⊆
                interior (closure (interior (A ∪ B ∪ C))) := by
            apply interior_mono
            apply closure_mono
            apply interior_mono
            intro y hy
            -- `y ∈ A` is certainly in `A ∪ B ∪ C`
            exact Or.inl (Or.inl hy)
          exact hSub hA
      | inr hB =>
          -- Handle the case `x ∈ interior (closure (interior B))`
          have hSub :
              interior (closure (interior B)) ⊆
                interior (closure (interior (A ∪ B ∪ C))) := by
            apply interior_mono
            apply closure_mono
            apply interior_mono
            intro y hy
            -- `y ∈ B` embeds into the union
            exact Or.inl (Or.inr hy)
          exact hSub hB
  | inr hC =>
      -- Handle the case `x ∈ interior (closure (interior C))`
      have hSub :
          interior (closure (interior C)) ⊆
            interior (closure (interior (A ∪ B ∪ C))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        -- `y ∈ C` embeds into the union
        exact Or.inr hy
      exact hSub hC



theorem Topology.closure_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hSub : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
        apply closure_mono
        exact Set.subset_union_left
      exact hSub hxA
  | inr hxB =>
      have hSub : closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
        apply closure_mono
        exact Set.subset_union_right
      exact hSub hxB

theorem Topology.subset_closure_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  intro x hx
  rcases hx with hxA | hxB
  ·
    have : (x : X) ∈ closure (A ∪ B : Set X) :=
      (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)) hxA
    exact this
  ·
    have : (x : X) ∈ closure (A ∪ B : Set X) :=
      (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)) hxB
    exact this



theorem Topology.interior_inter_interiors_eq
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  -- `interior A` and `interior B` are open sets.
  have hA : IsOpen (interior A) := isOpen_interior
  have hB : IsOpen (interior B) := isOpen_interior
  -- Apply the general lemma for the interior of an intersection of open sets.
  simpa using (interior_inter hA hB)

theorem Topology.isClosed_of_closureInterior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (A : Set X)) :
    IsClosed (A : Set X) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa [h] using hClosed

theorem Topology.IsOpen_P1_P2_P3_inter_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∩ B ∩ C) ∧ Topology.P2 (A ∩ B ∩ C) ∧ Topology.P3 (A ∩ B ∩ C) := by
  have hOpen : IsOpen (A ∩ B ∩ C) := ((hA.inter hB).inter hC)
  simpa using Topology.IsOpen_P1_P2_P3 (A := A ∩ B ∩ C) hOpen

theorem Topology.interiorClosure_interInteriors_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Inclusion into `interior (closure (interior A))`.
  have hA : x ∈ interior (closure (interior A)) := by
    have hSub : closure (interior A ∩ interior B) ⊆ closure (interior A) := by
      apply closure_mono
      intro y hy
      exact hy.1
    have hSubInt : interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior A)) :=
      interior_mono hSub
    exact hSubInt hx
  -- Inclusion into `interior (closure (interior B))`.
  have hB : x ∈ interior (closure (interior B)) := by
    have hSub : closure (interior A ∩ interior B) ⊆ closure (interior B) := by
      apply closure_mono
      intro y hy
      exact hy.2
    have hSubInt : interior (closure (interior A ∩ interior B)) ⊆
        interior (closure (interior B)) :=
      interior_mono hSub
    exact hSubInt hx
  exact And.intro hA hB

theorem Topology.P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- The density assumption forces both properties to hold unconditionally.
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDense
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) hDense
  constructor
  · intro _; exact hP3
  · intro _; exact hP2

theorem Topology.interior_nonempty_iff_nonempty_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    (interior A).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    rcases hInt with ⟨x, hx⟩
    exact ⟨x, (interior_subset : (interior A : Set X) ⊆ A) hx⟩
  · intro hA
    exact Topology.interior_nonempty_of_P1 (A := A) hP1 hA

theorem Topology.nonempty_inter_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A.Nonempty → (A ∩ interior (closure A)).Nonempty := by
  intro hP3 hA
  rcases hA with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  exact ⟨x, And.intro hxA hxInt⟩

theorem interior_inter_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∩ B ∩ C : Set X) = A ∩ B ∩ C := by
  have hOpen : IsOpen (A ∩ B ∩ C : Set X) := by
    have hAB : IsOpen (A ∩ B : Set X) := hA.inter hB
    exact hAB.inter hC
  simpa using hOpen.interior_eq

theorem Topology.isOpen_closureInterior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hOpen : IsOpen (closure (A : Set X))) :
    IsOpen (closure (interior A)) := by
  have hEq : closure (interior A) = closure (A : Set X) :=
    Topology.closureInterior_eq_closure_of_P2 (A := A) hP2
  simpa [hEq] using hOpen

theorem Topology.closure_union_three_subset {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    closure (A : Set X) ∪ closure (B : Set X) ∪ closure (C : Set X) ⊆
      closure (A ∪ B ∪ C : Set X) := by
  intro x hx
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA =>
          -- Case `x ∈ closure A`
          have hSub : (A : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inl hy)
          exact (closure_mono hSub) hA
      | inr hB =>
          -- Case `x ∈ closure B`
          have hSub : (B : Set X) ⊆ A ∪ B ∪ C := by
            intro y hy
            exact Or.inl (Or.inr hy)
          exact (closure_mono hSub) hB
  | inr hC =>
      -- Case `x ∈ closure C`
      have hSub : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      exact (closure_mono hSub) hC

theorem Topology.interior_iInter_closure_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    interior (⋂ i, closure (F i) : Set X) ⊆ ⋂ i, interior (closure (F i)) := by
  intro x hx
  have h : ∀ i, x ∈ interior (closure (F i)) := by
    intro i
    have hSub : (⋂ j, closure (F j) : Set X) ⊆ closure (F i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have hIncl : interior (⋂ j, closure (F j) : Set X) ⊆ interior (closure (F i)) :=
      interior_mono hSub
    exact hIncl hx
  exact Set.mem_iInter.2 h

theorem Topology.isOpen_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = A → IsOpen (A : Set X) := by
  intro h
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h] using this

theorem Topology.P3_superset_of_subset_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  have hxIntA : x ∈ interior (closure (interior A)) := hBsubset hxB
  have hMono₁ :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) :=
    Topology.interiorClosureInterior_mono hAB
  have hMono₂ :
      interior (closure (interior B)) ⊆ interior (closure B) :=
    Topology.interiorClosureInterior_subset_interiorClosure (A := B)
  exact hMono₂ (hMono₁ hxIntA)

theorem Topology.P2_inter_interiors {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior A ∩ interior B) := by
  have hOpen : IsOpen ((interior A) ∩ (interior B) : Set X) :=
    isOpen_interior.inter isOpen_interior
  exact Topology.IsOpen_P2 (A := interior A ∩ interior B) hOpen

theorem Topology.closureInterior_inter_eq_closure_inter_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  -- For an open set, its interior is itself.
  have hInt : interior (A ∩ B) = A ∩ B := hOpen.interior_eq
  -- Substitute and simplify.
  simpa [hInt]

theorem Topology.P1_interiorClosureClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (closure (A : Set X)))) := by
  simpa [closure_closure] using
    (Topology.P1_interiorClosure (A := A))

theorem Topology.P2_inter_open_three {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    IsOpen A → IsOpen B → IsOpen C → Topology.P2 (A ∩ B ∩ C) := by
  intro hA hB hC
  have hOpen : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := hA.inter hB
    exact hAB.inter hC
  exact IsOpen_P2 (A := A ∩ B ∩ C) hOpen

theorem Topology.interiorClosure_mono_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : closure (A : Set X) ⊆ closure (B : Set X)) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  exact interior_mono h

theorem Topology.P3_of_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = A) : Topology.P3 A := by
  -- The hypothesis yields the openness of `A`.
  have hOpen : IsOpen (A : Set X) := by
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [h] using this
  -- Every open set satisfies `P3`.
  exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen).2

theorem Topology.interior_inter_closures_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hA : x ∈ interior (closure (A : Set X)) := by
    have hSub : (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (A : Set X) := by
      intro y hy
      exact hy.1
    exact (interior_mono hSub) hx
  -- Membership in `interior (closure B)`
  have hB : x ∈ interior (closure (B : Set X)) := by
    have hSub : (closure (A : Set X) ∩ closure (B : Set X)) ⊆ closure (B : Set X) := by
      intro y hy
      exact hy.2
    exact (interior_mono hSub) hx
  exact And.intro hA hB

theorem Topology.P3_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 (Aᶜ) := by
  -- We already have a result giving all three properties for the complement of a closed set.
  -- Extract the `P3` component from that result.
  have h := (Topology.P1_P2_P3_compl_of_closed (A := A) hA)
  exact h.2.2

theorem Topology.interiorClosure_inter_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure (A ∩ B ∩ C)) ⊆
      interior (closure A) ∩ interior (closure B) ∩ interior (closure C) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hA : x ∈ interior (closure A) := by
    have hSub : closure (A ∩ B ∩ C) ⊆ closure A := by
      apply closure_mono
      intro y hy
      exact hy.1.1
    exact (interior_mono hSub) hx
  -- Membership in `interior (closure B)`
  have hB : x ∈ interior (closure B) := by
    have hSub : closure (A ∩ B ∩ C) ⊆ closure B := by
      apply closure_mono
      intro y hy
      exact hy.1.2
    exact (interior_mono hSub) hx
  -- Membership in `interior (closure C)`
  have hC : x ∈ interior (closure C) := by
    have hSub : closure (A ∩ B ∩ C) ⊆ closure C := by
      apply closure_mono
      intro y hy
      exact hy.2
    exact (interior_mono hSub) hx
  exact ⟨⟨hA, hB⟩, hC⟩

theorem Topology.closureInterior_inter_subset_closure_interInteriors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- Start from the basic inclusion
  -- `interior (A ∩ B) ⊆ interior A ∩ interior B`.
  have h :
      (interior (A ∩ B) : Set X) ⊆ interior A ∩ interior B :=
    Topology.interior_inter_subset_inter_interior (A := A) (B := B)
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono h