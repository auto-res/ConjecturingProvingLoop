

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  unfold Topology.P2 Topology.P1 at *
  intro x hx
  have h' : x ∈ interior (closure (interior A)) := h hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) h'

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  unfold Topology.P2 Topology.P3 at *
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_mono : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    exact closure_mono (interior_subset : interior A ⊆ A)
  exact h_mono hx₁

theorem Topology.P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  unfold Topology.P3
  intro x hx
  have hsubset : A ⊆ interior (closure A) := interior_maximal subset_closure hA
  exact hsubset hx

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  unfold Topology.P1 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ closure (interior A) := hA hxA
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left)
      have hclosure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hx₁
  | inr hxB =>
      have hx₁ : x ∈ closure (interior B) := hB hxB
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right)
      have hclosure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hx₁

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  unfold Topology.P1
  intro x hx
  have h : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using h

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  unfold Topology.P2
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    have h₁ : interior A ⊆ closure (interior A) := subset_closure
    exact interior_maximal h₁ isOpen_interior
  simpa [interior_interior] using hsubset hx

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  simpa using (Topology.P3_of_isOpen (A := interior A) isOpen_interior)

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  unfold Topology.P1
  intro x hx
  cases hx

theorem Topology.P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  unfold Topology.P2
  intro x hx
  have hsubset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  have : x ∈ interior (closure A) := hsubset hx
  simpa [hA.interior_eq] using this

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  unfold Topology.P3 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ interior (closure A) := hA hxA
      have hsubset_closure : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx₁
  | inr hxB =>
      have hx₁ : x ∈ interior (closure B) := hB hxB
      have hsubset_closure : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hx₁

theorem Topology.P1_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  unfold Topology.P1
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  unfold Topology.P2 at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx₁ : x ∈ interior (closure (interior A)) := hA hxA
      have hsubset_int : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hsubset_clos : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      have hsubset : interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_clos
      exact hsubset hx₁
  | inr hxB =>
      have hx₁ : x ∈ interior (closure (interior B)) := hB hxB
      have hsubset_int : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hsubset_clos : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset_int
      have hsubset : interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono hsubset_clos
      exact hsubset hx₁

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Dense A) : Topology.P3 A := by
  unfold Topology.P3
  intro x hx
  have hclosure : closure A = (Set.univ : Set X) := hA.closure_eq
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hclosure] using interior_univ
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt] using this

theorem Topology.closure_interior_eq_of_closed_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hP1 : Topology.P1 A) :
    closure (interior A) = A := by
  apply subset_antisymm
  ·
    have h : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [hA_closed.closure_eq] using h
  ·
    exact hP1

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact
    ⟨Topology.P2_implies_P1 (A := A) hP2, Topology.P2_implies_P3 (A := A) hP2⟩

theorem Topology.P_properties_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.P1_of_isOpen (A := A) hA,
      ⟨Topology.P2_of_isOpen (A := A) hA,
        Topology.P3_of_isOpen (A := A) hA⟩⟩

theorem Topology.P_properties_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧
      Topology.P3 (Set.univ : Set X) := by
  simpa using
    (Topology.P_properties_of_isOpen (A := (Set.univ : Set X)) isOpen_univ)

theorem Topology.P1_iff_closure_interior_eq_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_closed_of_P1 (A := A) hA_closed hP1
  · intro h_eq
    unfold Topology.P1
    intro x hx
    simpa [h_eq] using hx

theorem Topology.closure_interior_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior A) = closure A := by
  apply subset_antisymm
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)
  ·
    have h₁ : A ⊆ closure (interior A) := hP1
    have h₂ : closure A ⊆ closure (closure (interior A)) := closure_mono h₁
    simpa [closure_closure] using h₂

theorem Topology.P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
  · intro h_eq
    unfold Topology.P1
    intro x hx
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this

theorem Topology.isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) : IsOpen A := by
  have h_subset : A ⊆ interior A := by
    intro x hx
    have : x ∈ interior (closure A) := hP3 hx
    simpa [hA_closed.closure_eq] using this
  have h_eq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact h_subset
  simpa [h_eq] using (isOpen_interior : IsOpen (interior A))

theorem Topology.interior_eq_self_of_closed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  apply subset_antisymm
  ·
    exact interior_subset
  ·
    intro x hxA
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hA_closed.closure_eq] using this

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  · intro hOpen
    exact Topology.P3_of_isOpen (A := A) hOpen

theorem Topology.isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  have h_closure_subset : closure (interior A) ⊆ A := by
    have h_sub : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [hA_closed.closure_eq] using h_sub
  have h_int_subset : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h_closure_subset
  have h_subset : A ⊆ interior A := by
    intro x hxA
    have : x ∈ interior (closure (interior A)) := hP2 hxA
    exact h_int_subset this
  have h_eq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact h_subset
  simpa [h_eq] using (isOpen_interior : IsOpen (interior A))

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    exact Topology.isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  · intro hOpen
    exact Topology.P2_of_isOpen (A := A) hOpen

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : Dense (interior A)) : Topology.P1 A := by
  unfold Topology.P1
  intro x hxA
  have h_closure : closure (interior A) = (Set.univ : Set X) := h_dense.closure_eq
  have h_univ : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h_closure] using h_univ

theorem Topology.interior_eq_self_of_closed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  have hOpen : IsOpen A := Topology.isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  simpa using hOpen.interior_eq

theorem Topology.P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 A → Topology.P2 A := by
  intro hP3
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  exact Topology.P2_of_isOpen (A := A) hOpen

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h1 : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed
  have h2 : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed
  exact h1.trans h2.symm

theorem Topology.closure_interior_eq_closure_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) :
    closure (interior A) = closure A := by
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact Topology.closure_interior_eq_closure_of_P1 (A := A) hP1

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  unfold Topology.P2
  intro x hx
  cases hx

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  unfold Topology.P3
  intro x hx
  cases hx

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  unfold Topology.P1
  intro x hx
  have h_sub : interior A ⊆ interior (closure (interior A)) := by
    have : interior (interior A) ⊆ interior (closure (interior A)) := by
      apply interior_mono
      exact subset_closure
    simpa [interior_interior] using this
  have h_closure : closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono h_sub
  exact h_closure hx

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P1 (A i)) → Topology.P1 (Set.iUnion A) := by
  intro h
  unfold Topology.P1
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx₁ : x ∈ closure (interior (A i)) := h i hxA
  have hsubset : interior (A i) ⊆ interior (Set.iUnion A) :=
    interior_mono (Set.subset_iUnion A i)
  have hclosure : closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) :=
    closure_mono hsubset
  exact hclosure hx₁

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P3 (A i)) → Topology.P3 (Set.iUnion A) := by
  intro h
  unfold Topology.P3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx₁ : x ∈ interior (closure (A i)) := h i hxA
  have hsubset_closure : closure (A i) ⊆ closure (Set.iUnion A) :=
    closure_mono (Set.subset_iUnion A i)
  have hsubset : interior (closure (A i)) ⊆ interior (closure (Set.iUnion A)) :=
    interior_mono hsubset_closure
  exact hsubset hx₁

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : Dense (interior A)) : Topology.P2 A := by
  unfold Topology.P2
  intro x hxA
  have hclosure : closure (interior A) = (Set.univ : Set X) := h_dense.closure_eq
  have hint : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [hclosure] using interior_univ
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hint] using this

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P2 (Set.iUnion A) := by
  intro h
  unfold Topology.P2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx₁ : x ∈ interior (closure (interior (A i))) := h i hxA
  have hsubset_int : interior (A i) ⊆ interior (Set.iUnion A) :=
    interior_mono (Set.subset_iUnion A i)
  have hsubset_clos : closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) :=
    closure_mono hsubset_int
  have hsubset : interior (closure (interior (A i))) ⊆
      interior (closure (interior (Set.iUnion A))) :=
    interior_mono hsubset_clos
  exact hsubset hx₁

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  have h := Topology.P_properties_univ (X := X)
  exact h.right.right

theorem Topology.P3_iUnion_of_P2 {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P3 (Set.iUnion A) := by
  intro hP2
  have hP3 : ∀ i, Topology.P3 (A i) :=
    fun i => Topology.P2_implies_P3 (A := A i) (hP2 i)
  exact Topology.P3_iUnion (A := A) hP3

theorem Topology.P_properties_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : Dense (interior A)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A := Topology.P1_of_dense_interior (A := A) h_dense
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) h_dense
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact ⟨hP1, ⟨hP2, hP3⟩⟩

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P3 A := by
  -- First, obtain P2 for `A` from the density of `interior A`
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDense
  -- Then, derive P3 from P2
  exact Topology.P2_implies_P3 (A := A) hP2

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  simpa using
    (Topology.P2_of_isOpen (A := interior (closure A)) isOpen_interior)

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  simpa using
    (Topology.P3_of_isOpen (A := interior (closure A)) isOpen_interior)

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P1 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro h
  unfold Topology.P1
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A : Topology.P1 A := h A hA_mem
  have hx₁ : x ∈ closure (interior A) := hP1A hxA
  have hsubset : interior A ⊆ interior (⋃₀ 𝒜) := by
    have hA_subset : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
    exact interior_mono hA_subset
  have hclosure : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset
  exact hclosure hx₁

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P3 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro h
  unfold Topology.P3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP3A : Topology.P3 A := h A hA_mem
  have hx₁ : x ∈ interior (closure A) := hP3A hxA
  have hsubset_closure : closure A ⊆ closure (⋃₀ 𝒜) :=
    closure_mono (Set.subset_sUnion_of_mem hA_mem)
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) :=
    interior_mono hsubset_closure
  exact hsubset hx₁

theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  unfold Topology.P1
  intro x hx
  have h_subset : A ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  have h_closure_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono h_subset
  exact h_closure_subset hx

theorem Topology.closure_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply subset_antisymm
  ·
    -- `LHS ⊆ RHS`
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆ closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    -- `RHS ⊆ LHS`
    have h₁ : interior A ⊆ interior (closure (interior A)) := by
      have h_sub : interior A ⊆ closure (interior A) := subset_closure
      exact interior_maximal h_sub isOpen_interior
    have h₂ : closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂

theorem Topology.P3_sUnion_of_P2 {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hP2
  have hP3 : ∀ A, A ∈ 𝒜 → Topology.P3 A := by
    intro A hA
    exact Topology.P2_implies_P3 (A := A) (hP2 A hA)
  exact Topology.P3_sUnion (X := X) (𝒜 := 𝒜) hP3

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  simpa using (Topology.P_properties_univ (X := X)).right.left

theorem Topology.P1_iUnion_of_P2 {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P1 (Set.iUnion A) := by
  intro hP2
  have hP1 : ∀ i, Topology.P1 (A i) := fun i =>
    Topology.P2_implies_P1 (A := A i) (hP2 i)
  exact Topology.P1_iUnion (A := A) hP1

theorem Topology.P2_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior A))) := by
  simpa using
    (Topology.P2_of_isOpen (A := interior (closure (interior A))) isOpen_interior)

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  simpa using
    (Topology.P1_of_isOpen (A := interior (closure A)) isOpen_interior)

theorem Topology.P3_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior A))) := by
  simpa using
    (Topology.P3_of_isOpen (A := interior (closure (interior A))) isOpen_interior)

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P2_iff_P3_of_isClosed (A := closure A) h_closed)

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  unfold Topology.P1 at *
  intro x hx
  have h_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact h_subset hx

theorem Topology.P1_sUnion_of_P2 {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hP2
  -- Derive P1 for every set in 𝒜 from the assumed P2 property
  have hP1 : ∀ A, A ∈ 𝒜 → Topology.P1 A := by
    intro A hA
    exact Topology.P2_implies_P1 (A := A) (hP2 A hA)
  -- Apply the existing `P1_sUnion` theorem
  exact Topology.P1_sUnion (X := X) (𝒜 := 𝒜) hP1

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    -- Since `A` is open, `P2` always holds for `A`.
    unfold Topology.P2
    intro x hxA
    have h_subset : A ⊆ interior (closure A) :=
      interior_maximal subset_closure hOpen
    have hxInt : x ∈ interior (closure A) := h_subset hxA
    simpa [hOpen.interior_eq] using hxInt
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → Topology.P2 A) → Topology.P2 (⋃₀ 𝒜) := by
  intro h
  unfold Topology.P2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := h A hA_mem
  have hx₁ : x ∈ interior (closure (interior A)) := hP2A hxA
  have hsubset_int : interior A ⊆ interior (⋃₀ 𝒜) :=
    interior_mono (Set.subset_sUnion_of_mem hA_mem)
  have hsubset_clos : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
    closure_mono hsubset_int
  have hsubset : interior (closure (interior A)) ⊆
      interior (closure (interior (⋃₀ 𝒜))) :=
    interior_mono hsubset_clos
  exact hsubset hx₁

theorem Topology.interior_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply subset_antisymm
  ·
    -- `LHS ⊆ RHS`
    have h₁ : closure (interior (closure A)) ⊆ closure A := by
      have : interior (closure A) ⊆ closure A := interior_subset
      have h := closure_mono this
      simpa [closure_closure] using h
    have : interior (closure (interior (closure A))) ⊆ interior (closure A) :=
      interior_mono h₁
    exact this
  ·
    -- `RHS ⊆ LHS`
    have h_subset : interior (closure A) ⊆ closure (interior (closure A)) :=
      subset_closure
    have h_isOpen : IsOpen (interior (closure A)) := isOpen_interior
    have : interior (closure A) ⊆ interior (closure (interior (closure A))) :=
      interior_maximal h_subset h_isOpen
    exact this

theorem Topology.closure_interior_idempotent_iter {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
      simpa using
        (Topology.closure_interior_idempotent (A := closure (interior A)))
    _ = closure (interior A) := by
      simpa using
        (Topology.closure_interior_idempotent (A := A))

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  constructor
  · intro _hP1
    exact Topology.P3_of_isOpen (A := A) hA
  · intro _hP3
    exact Topology.P1_of_isOpen (A := A) hA

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  exact (Topology.P_properties_univ (X := X)).left

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  simpa using h₁.symm.trans h₂

theorem Topology.interior_closure_idempotent_iter2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using
            (Topology.interior_closure_idempotent (A := interior (closure A)))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_idempotent (A := A))

theorem Topology.interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- Since `interior A ⊆ A`, applying `closure` preserves the inclusion,
  -- and then `interior_mono` yields the desired result.
  apply interior_mono
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  -- Unfold the definition of `P1`
  unfold Topology.P1 at *
  intro x hx
  -- Step 1: `closure A ⊆ closure (interior A)`
  have h₁ : closure A ⊆ closure (interior A) := by
    -- `closure_mono` applied to `hP1`
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using this
  -- Step 2: `closure (interior A) ⊆ closure (interior (closure A))`
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- First, `interior A ⊆ interior (closure A)`
    have h_int : interior A ⊆ interior (closure A) := by
      apply interior_mono
      exact subset_closure
    -- Taking closures preserves the inclusion
    exact closure_mono h_int
  -- Combine the two inclusions to get the desired subset relation
  have h_subset : closure A ⊆ closure (interior (closure A)) :=
    Set.Subset.trans h₁ h₂
  exact h_subset hx

theorem Topology.P1_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  -- A closed set satisfying `P3` is open
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- Every open set satisfies `P1`
  exact Topology.P1_of_isOpen (A := A) hA_open

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  unfold Topology.P3 at *
  intro x hxA
  have hx_closure : x ∈ closure A := subset_closure hxA
  have hx_int : x ∈ interior (closure (closure A)) := hP3 hx_closure
  simpa [closure_closure] using hx_int

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- Step 1: `interior A ⊆ interior (closure A)`
  have h_int : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  -- Step 2: Apply `closure_mono` to get the desired inclusion
  exact closure_mono h_int

theorem Topology.interior_closure_idempotent_iter3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure (interior (closure (interior (closure A))))) := by
          simpa using
            (Topology.interior_closure_idempotent
              (A := interior (closure (interior (closure A)))))
    _ = interior (closure (interior (closure A))) := by
          simpa using
            (Topology.interior_closure_idempotent (A := interior (closure A)))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_idempotent (A := A))

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) := by
  simpa using
    (Topology.P1_of_isOpen (A := interior (closure (interior A))) isOpen_interior)

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_subset : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono h_subset)

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  have hCl : closure A ⊆ closure B := closure_mono hAB
  exact interior_mono hCl

theorem Topology.closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- First, `interior (closure A)` is contained in `closure A`.
  have h : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusions; simplify `closure (closure A)`.
  simpa [closure_closure] using closure_mono h

theorem Topology.P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    exact Topology.interior_eq_self_of_closed_and_P3 (A := A) hA_closed hP3
  · intro h_int
    -- From `interior A = A`, we get that `A` is open.
    have hA_open : IsOpen A := by
      simpa [h_int] using (isOpen_interior : IsOpen (interior A))
    -- Every open set satisfies `P3`.
    simpa using (Topology.P3_of_isOpen (A := A) hA_open)

theorem Topology.interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense A) :
    interior (closure A) = (Set.univ : Set X) := by
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_closure] using
    (interior_univ : interior (Set.univ : Set X) = Set.univ)

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) :
    A = (Set.univ : Set X) := by
  -- Since `A` is closed, its closure is itself.
  have h₁ : closure A = A := hClosed.closure_eq
  -- Since `A` is dense, its closure is the whole space.
  have h₂ : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Combining the two equalities yields the desired result.
  simpa [h₁] using h₂

theorem Topology.P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using (Topology.P3_iff_isOpen_of_isClosed (A := closure A) hClosed)

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure A) := by
  -- `interior` is monotone, and `A` is always contained in its closure.
  exact interior_mono (subset_closure : A ⊆ closure A)

theorem Topology.closure_interior_closure_eq_univ_of_dense {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Consequently, the interior of its closure is also the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure] using interior_univ
  -- Taking the closure again yields the whole space.
  calc
    closure (interior (closure A))
        = closure (Set.univ : Set X) := by
          simpa [h_int]
    _ = (Set.univ : Set X) := by
          simpa using closure_univ

theorem Topology.P1_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) : Topology.P1 A := by
  -- First, deduce that `A` is open from its being closed and satisfying `P2`.
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  -- Every open set satisfies `P1`.
  exact Topology.P1_of_isOpen (A := A) hA_open

theorem Topology.interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior A)))) = interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_idempotent (A := interior A))

theorem Topology.P2_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  constructor
  · intro hP2
    exact Topology.interior_eq_self_of_closed_and_P2 (A := A) hA_closed hP2
  · intro hInt
    have hA_open : IsOpen A := by
      simpa [hInt] using (isOpen_interior : IsOpen (interior A))
    exact Topology.P2_of_isOpen (A := A) hA_open

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  unfold Topology.P1
  intro x hx
  -- `closure (interior (closure (interior (closure A))))`
  -- coincides with `closure (interior (closure A))`
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_idempotent (A := closure A))
  -- Use the equality to convert the membership hypothesis
  simpa [h_eq] using hx

theorem Topology.interior_closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) :
    interior (closure A) = (Set.univ : Set X) := by
  -- The density of `interior A` implies its closure is the whole space.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- `closure (interior A)` is contained in `closure A`.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Hence, `closure A` is also the whole space.
  have h_closureA : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _x _hx; simp
    ·
      have : (Set.univ : Set X) ⊆ closure A := by
        have : closure (interior A) ⊆ closure A := h_subset
        simpa [h_closure_int] using this
      exact this
  -- Taking interiors yields the desired equality.
  simpa [h_closureA] using
    (interior_univ : interior (Set.univ : Set X) = Set.univ)

theorem Topology.closure_interior_idempotent_iter4 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior (closure (interior A))))) := by
          simpa using
            (Topology.closure_interior_idempotent
              (A := closure (interior (closure (interior A)))))
    _ = closure (interior (closure (interior A))) := by
          simpa using
            (Topology.closure_interior_idempotent
              (A := closure (interior A)))
    _ = closure (interior A) := by
          simpa using
            (Topology.closure_interior_idempotent (A := A))

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h₁ : Topology.P2 (closure A) ↔ Topology.P3 (closure A) :=
    Topology.P2_closure_iff_P3_closure (A := A)
  have h₂ : Topology.P3 (closure A) ↔ IsOpen (closure A) :=
    Topology.P3_closure_iff_isOpen_closure (A := A)
  exact h₁.trans h₂

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact Topology.P3_implies_P1_closure (A := A) hP3

theorem Topology.P3_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P3 (closure A) := by
  unfold Topology.P3
  intro x hx
  -- `A` is dense, so its closure is the whole space.
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the interior of its closure is also the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Trivially, every point lies in `Set.univ`.
  have : x ∈ (Set.univ : Set X) := by
    simp
  -- Conclude using the equality for interiors.
  simpa [h_int] using this

theorem Topology.P1_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P1 (closure A) := by
  -- `A` is dense, so its closure is the whole space.
  have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- We already know that `P1` holds for `Set.univ`.
  have hP1_univ : Topology.P1 (Set.univ : Set X) := Topology.P1_univ (X := X)
  -- Rewriting along the equality gives the desired result.
  simpa [h_closure] using hP1_univ

theorem Topology.closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  exact interior_mono (closure_mono (interior_mono hAB))

theorem Topology.subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1B : Topology.P1 B) :
    A ⊆ closure (interior B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP1B hxB

theorem Topology.P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P2 (closure A) := by
  -- Obtain `P3` for `closure A` from the density of `A`.
  have hP3 : Topology.P3 (closure A) :=
    Topology.P3_closure_of_dense (A := A) hDense
  -- Use the equivalence `P2 (closure A) ↔ P3 (closure A)` to get `P2`.
  exact (Topology.P2_closure_iff_P3_closure (A := A)).2 hP3

theorem Topology.interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- First, note that `interior A ⊆ closure (interior A)`.
  have h : interior A ⊆ closure (interior A) := subset_closure
  -- Applying the monotonicity of `interior` yields the desired inclusion.
  have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h
  -- Finally, rewrite `interior (interior A)` to `interior A`.
  simpa [interior_interior] using h'

theorem Topology.P_properties_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) :
    Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP1 : Topology.P1 (closure A) := Topology.P1_closure_of_dense (A := A) hDense
  have hP2 : Topology.P2 (closure A) := Topology.P2_closure_of_dense (A := A) hDense
  have hP3 : Topology.P3 (closure A) := Topology.P3_closure_of_dense (A := A) hDense
  exact ⟨hP1, ⟨hP2, hP3⟩⟩

theorem Topology.subset_interior_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  exact hP2B (hAB hxA)

theorem Topology.subset_interior_closure_of_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (closure A)) :
    A ⊆ interior (closure A) := by
  intro x hxA
  -- First, note that `x ∈ closure A`.
  have hx_closure : x ∈ closure A := subset_closure hxA
  -- Apply the `P3` property for `closure A`.
  have hx_int : x ∈ interior (closure (closure A)) := hP3 hx_closure
  -- Simplify `interior (closure (closure A))` to `interior (closure A)`.
  simpa [closure_closure] using hx_int

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, use the monotonicity of `interior ∘ closure` under the assumption `A ⊆ B`.
  have h₁ : interior (closure A) ⊆ interior (closure B) :=
    Topology.interior_closure_mono (A := A) (B := B) hAB
  -- Taking closures preserves inclusions.
  exact closure_mono h₁

theorem Topology.subset_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP3B : Topology.P3 B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  have hxB : x ∈ B := hAB hxA
  exact hP3B hxB

theorem Topology.closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x` belongs to `closure (interior A)`
  have hxA : x ∈ closure (interior A) := by
    have hsubset : interior (A ∩ B) ⊆ interior A :=
      interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
    exact (closure_mono hsubset) hx
  -- Show `x` belongs to `closure (interior B)`
  have hxB : x ∈ closure (interior B) := by
    have hsubset : interior (A ∩ B) ⊆ interior B :=
      interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
    exact (closure_mono hsubset) hx
  exact And.intro hxA hxB

theorem Topology.closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hclosure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hxA
  | inr hxB =>
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hclosure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono hsubset
      exact hclosure hxB

theorem Topology.closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem Topology.interior_closure_interior_closure_eq_univ_of_dense {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    interior (closure (interior (closure A))) = (Set.univ : Set X) := by
  -- First, `interior (closure A)` is the whole space because `A` is dense.
  have h_int : interior (closure A) = (Set.univ : Set X) :=
    Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  -- Consequently, its closure is also the whole space.
  have h_closure : closure (interior (closure A)) = (Set.univ : Set X) := by
    simpa [h_int] using (closure_univ : closure (Set.univ : Set X) = Set.univ)
  -- Taking the interior again still yields the whole space.
  simpa [h_closure] using (interior_univ : interior (Set.univ : Set X) = Set.univ)

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Pairwise equivalences already established for open sets
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Combine them to obtain the desired equivalence
  constructor
  · intro hP1
    exact ⟨(h₁.mp hP1), (h₂.mp hP1)⟩
  · rintro ⟨hP2, _hP3⟩
    exact h₁.mpr hP2

theorem Topology.eq_empty_of_P1_and_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hInt : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  ·
    intro x hxA
    have hx : x ∈ closure (interior A) := hP1 hxA
    simpa [hInt, closure_empty] using hx
  ·
    exact Set.empty_subset _

theorem Topology.P1_closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior (closure A))))) := by
  -- First, simplify the nested `closure ∘ interior` expression using idempotence.
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_idempotent (A := closure A))
  -- We already know `P1` holds for `closure (interior (closure A))`.
  have hP1 : Topology.P1 (closure (interior (closure A))) :=
    Topology.P1_closure_interior_closure (A := A)
  -- Transport the property along the established equality.
  simpa [h_eq] using hP1

theorem Topology.eq_empty_of_P2_and_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hInt : interior A = (∅ : Set X)) :
    A = ∅ := by
  apply Set.Subset.antisymm
  ·
    intro x hxA
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    have hEmpty : x ∈ (∅ : Set X) := by
      simpa [hInt, closure_empty, interior_empty] using hxInt
    cases hEmpty
  ·
    exact Set.empty_subset _

theorem Topology.closure_interior_idempotent_iter5 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior A))))))))) =
        closure (interior (closure (interior (closure (interior
          (closure (interior A))))))) := by
          simpa using
            (Topology.closure_interior_idempotent
              (A := closure (interior (closure (interior (closure (interior A)))))))
    _ = closure (interior (closure (interior (closure (interior A))))) := by
          simpa using
            (Topology.closure_interior_idempotent
              (A := closure (interior (closure (interior A)))))
    _ = closure (interior (closure (interior A))) := by
          simpa using
            (Topology.closure_interior_idempotent
              (A := closure (interior A)))
    _ = closure (interior A) := by
          simpa using
            (Topology.closure_interior_idempotent (A := A))

theorem Topology.closure_union_interiors_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) = closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (s := interior A) (t := interior B)

theorem Topology.interior_closure_union_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure A)`
      have hsubset_closure : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior (closure B)`
      have hsubset_closure : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : B ⊆ A ∪ B)
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono hsubset_closure
      exact hsubset hxB

theorem Topology.interior_closure_inter_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    have h_subset : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure A) :=
      interior_mono h_subset
    exact h_int hx
  have hxB : x ∈ interior (closure B) := by
    have h_subset : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure B) :=
      interior_mono h_subset
    exact h_int hx
  exact And.intro hxA hxB

theorem Topology.closure_interior_eq_of_closed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- First, `interior A` coincides with `A` under the given assumptions.
  have h_int : interior A = A :=
    Topology.interior_eq_self_of_closed_and_P2 (A := A) hA_closed hP2
  -- Rewrite `closure (interior A)` using the above equality
  -- and use that `A` is closed.
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = A := hA_closed.closure_eq

theorem Topology.dense_iff_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact Topology.interior_closure_eq_univ_of_dense (A := A) hDense
  · intro hInt
    -- First, deduce `closure A = Set.univ`.
    have h_closure_univ : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _x _hx; simp
      ·
        have h_subset : interior (closure A) ⊆ closure A := interior_subset
        simpa [hInt] using h_subset
    -- Build the desired `Dense A`.
    have hDense : Dense A := by
      intro x
      have : x ∈ (Set.univ : Set X) := by simp
      simpa [h_closure_univ] using this
    exact hDense



theorem Topology.interior_closure_interior_eq_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure (interior A)) = interior (closure A) := by
  -- From `P1 A` we have the equality of closures.
  have hEq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
  -- Rewriting with `hEq` yields the desired equality of interiors.
  simpa [hEq]

theorem Topology.closure_union_interiors_eq_union_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (s := interior A) (t := interior B)

theorem Topology.union_interior_subset_interior_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact hsubset hA
  | inr hB =>
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      exact hsubset hB

theorem Topology.interior_closure_eq_interior_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA_closed.closure_eq]

theorem Topology.dense_iff_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ Dense (closure A) := by
  constructor
  · intro hDense
    have h_eq : closure A = (Set.univ : Set X) := hDense.closure_eq
    -- Deduce density of `closure A`.
    have hDenseClosure : Dense (closure A) := by
      intro x
      have hx : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [closure_closure, h_eq] using hx
    exact hDenseClosure
  · intro hDenseClosure
    have h_eq : closure A = (Set.univ : Set X) := by
      -- `closure (closure A) = Set.univ` implies `closure A = Set.univ`.
      simpa [closure_closure] using hDenseClosure.closure_eq
    -- Deduce density of `A`.
    have hDense : Dense A := by
      intro x
      have hx : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [h_eq] using hx
    exact hDense

theorem Topology.interior_closure_interior_eq_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP2 : Topology.P2 A) :
    interior (closure (interior A)) = interior (closure A) := by
  -- From `P2 A` we already have the equality of closures.
  have hEq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P2 (A := A) hP2
  -- Rewriting with `hEq` yields the desired equality of interiors.
  simpa [hEq]

theorem Topology.closure_interior_closure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    closure (interior (closure A)) = closure A := by
  apply subset_antisymm
  ·
    exact Topology.closure_interior_closure_subset_closure (A := A)
  ·
    have h_subset : A ⊆ interior (closure A) := hP3
    have : closure A ⊆ closure (interior (closure A)) := closure_mono h_subset
    exact this

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- First, show `interior A ⊆ ∅`.
    have h_sub : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    -- From the subset relation, obtain the desired equality.
    have h_eq : interior A = (∅ : Set X) := by
      apply Set.Subset.antisymm
      · exact h_sub
      · exact Set.empty_subset _
    exact h_eq
  · intro h
    simpa [h, closure_empty]

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    have hsubset : (A ∩ B) ⊆ A := Set.inter_subset_left
    exact (closure_mono hsubset) hx
  have hxB : x ∈ closure B := by
    have hsubset : (A ∩ B) ⊆ B := Set.inter_subset_right
    exact (closure_mono hsubset) hx
  exact And.intro hxA hxB

theorem Topology.dense_interior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ interior (closure (interior A)) = (Set.univ : Set X) := by
  simpa using
    (Topology.dense_iff_interior_closure_eq_univ (A := interior A))

theorem Topology.dense_iff_dense_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ Dense (interior (closure A)) := by
  constructor
  · intro hDenseA
    -- `closure A` is the whole space.
    have h_closureA : closure A = (Set.univ : Set X) := hDenseA.closure_eq
    -- Hence its interior is also the whole space.
    have h_int : interior (closure A) = (Set.univ : Set X) := by
      simpa [h_closureA] using (interior_univ :
        interior (Set.univ : Set X) = Set.univ)
    -- Consequently, the closure of that interior is the whole space.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) := by
      simpa [h_int] using (closure_univ :
        closure (Set.univ : Set X) = Set.univ)
    -- Turn the equality into a `Dense` statement.
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_closure_int] using this
  · intro hDenseInt
    -- The closure of `interior (closure A)` is the whole space.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) :=
      hDenseInt.closure_eq
    -- `closure (interior (closure A)) ⊆ closure A`.
    have h_subset : closure (interior (closure A)) ⊆ closure A :=
      Topology.closure_interior_closure_subset_closure (A := A)
    -- Therefore, `closure A` is also the whole space.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_closure_int] using h_subset
    have h_closureA : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _x _hx; simp
      · exact h_univ_subset
    -- Convert the equality into a `Dense` statement for `A`.
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_closureA] using this

theorem Topology.dense_interior_closure_iff_closure_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure A)) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- `Dense` gives the closure of `interior (closure A)` is the whole space.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) :=
      hDense.closure_eq
    -- This closure is contained in `closure A`.
    have h_subset : closure (interior (closure A)) ⊆ closure A :=
      Topology.closure_interior_closure_subset_closure (A := A)
    -- Hence `closure A` contains `Set.univ`, so the two sets coincide.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_closure_int] using h_subset
    have h_closure_subset : closure A ⊆ (Set.univ : Set X) := by
      intro x _; simp
    exact Set.Subset.antisymm h_closure_subset h_univ_subset
  · intro hClosure
    -- From `closure A = Set.univ`, it follows that `interior (closure A)` is `Set.univ`.
    have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
      simpa [hClosure] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
    -- Consequently, its closure is also `Set.univ`.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) := by
      simpa [h_int_univ] using
        (closure_univ : closure (Set.univ : Set X) = Set.univ)
    -- Reformulate this equality as the `Dense` property.
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_closure_int] using this

theorem Topology.closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ] using
    (closure_univ : closure (Set.univ : Set X) = Set.univ)

theorem Topology.P2_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (A := closure (interior A)) hClosed)

theorem Topology.interior_inter_eq_empty_of_closure_disjoint
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : closure A ∩ closure B = (∅ : Set X)) :
    interior (A ∩ B) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  ·
    -- First, show `interior (A ∩ B)` is contained in `closure A ∩ closure B`.
    have hsubset : interior (A ∩ B) ⊆ closure A ∩ closure B := by
      intro x hx
      have hxAB : x ∈ A ∩ B := interior_subset hx
      have hxA : x ∈ closure A := subset_closure hxAB.1
      have hxB : x ∈ closure B := subset_closure hxAB.2
      exact And.intro hxA hxB
    -- Rewriting with the hypothesis `h` gives the desired inclusion in `∅`.
    simpa [h] using hsubset
  ·
    exact Set.empty_subset _

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Step 1: `x ∈ interior (closure A)` by monotonicity of `interior`
  have hxIntClosure : x ∈ interior (closure A) := by
    have h_mono : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : A ⊆ closure A)
    exact h_mono hx
  -- Step 2: `interior (closure A)` is contained in its closure
  exact (subset_closure : interior (closure A) ⊆
      closure (interior (closure A))) hxIntClosure

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  -- First, we use an existing lemma to go from
  -- `interior (closure (interior A))` to `interior (closure A)`.
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure (A := A)
  -- Next, every set is contained in the closure of itself.
  have h₂ : interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  -- Combining the two inclusions gives the desired result.
  exact Set.Subset.trans h₁ h₂

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) :
    closure A = (Set.univ : Set X) := by
  -- First, density gives `closure (interior A) = Set.univ`.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Since `interior A ⊆ A`, their closures satisfy
  -- `closure (interior A) ⊆ closure A`.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Hence `Set.univ ⊆ closure A`.
  have h_superset : (Set.univ : Set X) ⊆ closure A := by
    simpa [h_closure_int] using h_subset
  -- The opposite inclusion is trivial.
  have h_subset_univ : closure A ⊆ (Set.univ : Set X) := by
    intro _x _hx; simp
  -- Conclude by antisymmetry.
  exact Set.Subset.antisymm h_subset_univ h_superset

theorem Topology.closure_interior_closure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    closure (interior (closure A)) = closure A := by
  apply Set.Subset.antisymm
  ·
    exact Topology.closure_interior_closure_subset_closure (A := A)
  ·
    -- From `P1 A` we have `closure (interior A) = closure A`.
    have h_eq : closure (interior A) = closure A :=
      Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
    -- Use monotonicity of `closure ∘ interior` under the inclusion `A ⊆ closure A`.
    have h_inc : closure (interior A) ⊆ closure (interior (closure A)) :=
      Topology.closure_interior_mono
        (A := A) (B := closure A) (subset_closure : A ⊆ closure A)
    -- Rewrite using `h_eq` to get the desired inclusion.
    simpa [h_eq] using h_inc

theorem Topology.P1_union_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hOpenB : IsOpen B) :
    Topology.P1 (A ∪ B) := by
  -- Obtain `P1` for `B` from its openness.
  have hP1B : Topology.P1 B := Topology.P1_of_isOpen (A := B) hOpenB
  -- Apply the existing union lemma for `P1`.
  exact Topology.P1_union (A := A) (B := B) hP1A hP1B

theorem Topology.P3_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (A := closure (interior A)) hClosed)

theorem Topology.interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- We show `closure A = Set.univ`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _hx
      -- Since `interior (closure A) = Set.univ`, every point lies in it.
      have : x ∈ interior (closure A) := by
        simpa [hInt] using (by
          have : x ∈ (Set.univ : Set X) := by
            simp
          exact this)
      exact interior_subset this
    have h_closure_subset : closure A ⊆ (Set.univ : Set X) := by
      intro x _hx
      simp
    exact Set.Subset.antisymm h_closure_subset h_univ_subset
  · intro hClosure
    -- From `closure A = Set.univ`, we immediately get the desired equality.
    simpa [hClosure] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)

theorem Topology.closure_interior_eq_self_iff_closed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = A ↔ (IsClosed A ∧ Topology.P1 A) := by
  constructor
  · intro h_eq
    have h_closed : IsClosed A := by
      have : IsClosed (closure (interior A)) := isClosed_closure
      simpa [h_eq] using this
    have h_P1 : Topology.P1 A := by
      intro x hx
      simpa [h_eq] using hx
    exact And.intro h_closed h_P1
  · rintro ⟨h_closed, h_P1⟩
    exact
      Topology.closure_interior_eq_of_closed_of_P1 (A := A) h_closed h_P1

theorem Topology.interior_diff_subset_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A \ closure B := by
  intro x hx_int
  -- `x` lies in the interior of `A`
  have hx_intA : x ∈ interior A := by
    have h_sub : (A \ B) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono h_sub) hx_int
  -- `x` is *not* in the closure of `B`
  have hx_not_clB : x ∉ closure B := by
    by_contra h_mem
    -- From `x ∈ closure B`, every open neighbourhood of `x` meets `B`
    -- in particular `interior (A \ B)` (which contains `x`) meets `B`
    have h_nonempty :
        (interior (A \ B) ∩ B).Nonempty := by
      have h_eq := (mem_closure_iff).1 h_mem
      exact h_eq _ isOpen_interior hx_int
    -- Extract a witness `y ∈ interior (A \ B) ∩ B`
    rcases h_nonempty with ⟨y, ⟨hy_int, hy_B⟩⟩
    -- But `interior (A \ B) ⊆ A \ B`, hence `y ∉ B` — contradiction
    have hy_notB : y ∉ B := by
      have : y ∈ A \ B :=
        (interior_subset : interior (A \ B) ⊆ A \ B) hy_int
      exact this.2
    exact hy_notB hy_B
  exact And.intro hx_intA hx_not_clB

theorem Topology.interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hA, hAc⟩
    have hA_mem : x ∈ A := interior_subset hA
    have hAc_mem : x ∈ Aᶜ := interior_subset hAc
    have : x ∈ A ∩ Aᶜ := ⟨hA_mem, hAc_mem⟩
    simpa [Set.inter_compl_self] using this
  · exact Set.empty_subset _

theorem Topology.P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ := Topology.P2_closure_interior_iff_isOpen_closure_interior (A := A)
  have h₂ := Topology.P3_closure_interior_iff_isOpen_closure_interior (A := A)
  exact h₁.trans h₂.symm

theorem Topology.P2_union_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen B) :
    Topology.P2 (A ∪ B) := by
  -- Obtain `P2` for the open set `B`.
  have hP2B : Topology.P2 B := Topology.P2_of_isOpen (A := B) hOpenB
  -- Apply the existing union lemma for `P2`.
  exact Topology.P2_union (A := A) (B := B) hP2A hP2B

theorem Topology.P3_union_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen B) :
    Topology.P3 (A ∪ B) := by
  -- `B` is open, hence satisfies `P3`.
  have hP3B : Topology.P3 B := Topology.P3_of_isOpen (A := B) hOpenB
  -- Apply the existing union lemma for `P3`.
  exact Topology.P3_union (A := A) (B := B) hP3A hP3B

theorem Topology.P3_closure_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P3 (closure A) := by
  unfold Topology.P3
  intro x hx
  -- `interior (closure A)` is the whole space because `interior A` is dense.
  have hInt : interior (closure A) = (Set.univ : Set X) :=
    Topology.interior_closure_eq_univ_of_dense_interior (A := A) hDense
  -- Therefore every point belongs to `interior (closure A)`.
  have hxInt : x ∈ interior (closure A) := by
    have : x ∈ (Set.univ : Set X) := by
      simp
    simpa [hInt] using this
  -- Rewrite to obtain membership in `interior (closure (closure A))`.
  simpa [closure_closure] using hxInt

theorem Topology.closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closure_interior_idempotent (A := closure A))

theorem Topology.P2_closure_interior_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) :
    Topology.P2 (closure (interior A)) := by
  -- Because `interior A` is dense, its closure is the whole space.
  have hEq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- `P2` holds for `Set.univ`; rewrite using `hEq`.
  simpa [hEq] using (Topology.P2_univ (X := X))

theorem Topology.P2_closure_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (interior A)))) ↔
      Topology.P2 (closure (interior A)) := by
  have hEq : closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_idempotent (A := A)
  simpa [hEq]

theorem Topology.P3_iUnion_isOpen {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hOpen : ∀ i, IsOpen (A i)) : Topology.P3 (Set.iUnion A) := by
  have hP3 : ∀ i, Topology.P3 (A i) := fun i =>
    Topology.P3_of_isOpen (A := A i) (hOpen i)
  exact Topology.P3_iUnion (A := A) hP3

theorem Topology.closure_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- First, `x` belongs to `closure A`.
  have h₁ : x ∈ closure A := by
    have h_subset : (A \ B) ⊆ A := by
      intro y hy
      exact hy.1
    exact (closure_mono h_subset) hx
  -- Next, prove `x ∉ interior B`.
  have h₂ : x ∉ interior B := by
    intro hxInt
    -- Consider the open set `interior B` that contains `x`.
    have h_nonempty : ((interior B) ∩ (A \ B)).Nonempty := by
      have h_open : IsOpen (interior B) := isOpen_interior
      exact (mem_closure_iff).1 hx (interior B) h_open hxInt
    -- Extract a witness from the non-empty intersection.
    rcases h_nonempty with ⟨y, ⟨hyIntB, hyDiff⟩⟩
    -- From `y ∈ interior B`, we get `y ∈ B`.
    have hy_in_B : y ∈ B := interior_subset hyIntB
    -- From `y ∈ A \\ B`, we know `y ∉ B`.
    have hy_not_B : y ∉ B := hyDiff.2
    exact hy_not_B hy_in_B
  exact And.intro h₁ h₂

theorem Topology.interior_diff_self_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior (A \ interior A) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in `A` but not in `interior A`
    have hxDiff : x ∈ A \ interior A := interior_subset hx
    -- Any open set contained in `A` is contained in `interior A`
    have h_subset : interior (A \ interior A) ⊆ interior A := by
      have h_open : IsOpen (interior (A \ interior A)) := isOpen_interior
      have h_subA : interior (A \ interior A) ⊆ A := by
        intro y hy; exact (interior_subset hy).1
      exact interior_maximal h_subA h_open
    -- Hence `x ∈ interior A`, contradiction
    have hxIntA : x ∈ interior A := h_subset hx
    exact (hxDiff.2 hxIntA)
  · exact Set.empty_subset _

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∪ B) = interior (A ∪ B) := rfl

theorem Topology.frontier_interior_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨h_clos, h_not_int⟩
  -- `x` lies in the closure of `A` because `interior A ⊆ A`.
  have h_closA : x ∈ closure A :=
    (closure_mono (interior_subset : interior A ⊆ A)) h_clos
  -- `x` is not in the interior of `A`.
  have h_not_intA : x ∉ interior A := by
    simpa [interior_interior] using h_not_int
  exact And.intro h_closA h_not_intA

theorem Topology.interior_closure_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.compl_closure_interior_eq_interior_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A))ᶜ = interior (closure (Aᶜ)) := by
  simpa [closure_compl] using
    (interior_compl (A := interior A)).symm

theorem Topology.closure_interior_eq_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : Dense (interior A)) :
    closure (interior A) = closure A := by
  -- Obtain `P2` for `A` from the density of its interior.
  have hP2 : Topology.P2 A := Topology.P2_of_dense_interior (A := A) hDense
  -- Use the existing lemma that equates the two closures under `P2`.
  exact Topology.closure_interior_eq_closure_of_P2 (A := A) hP2

theorem Topology.closure_interior_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    closure (interior A) = A := by
  calc
    closure (interior A) = closure A := by
      simpa [hA_open.interior_eq]
    _ = A := hA_closed.closure_eq

theorem Topology.closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- Start with the known relation for complements of closures of interiors.
  have h :
      (closure (interior (Aᶜ)))ᶜ = interior (closure A) := by
    simpa [compl_compl] using
      (Topology.compl_closure_interior_eq_interior_closure_compl (A := Aᶜ))
  -- Take complements of both sides of the equality `h`.
  have h' :
      ((closure (interior (Aᶜ)))ᶜ)ᶜ = (interior (closure A))ᶜ :=
    congrArg Set.compl h
  -- Simplify double complements to obtain the desired statement.
  simpa [compl_compl] using h'

theorem Topology.interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hA : x ∈ interior A := by
    have hsubset : (A ∩ B) ⊆ A := Set.inter_subset_left
    exact (interior_mono hsubset) hx
  have hB : x ∈ interior B := by
    have hsubset : (A ∩ B) ⊆ B := Set.inter_subset_right
    exact (interior_mono hsubset) hx
  exact And.intro hA hB

theorem Topology.nonempty_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  classical
  intro hP1 hAne
  rcases hAne with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  by_cases hIntEmpty : interior A = (∅ : Set X)
  · -- This case leads to a contradiction, since `x` cannot lie in `∅`.
    have hFalse : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using hx_cl
    exact False.elim hFalse
  · -- Here, `interior A` is non-empty.
    have h_ne : interior A ≠ (∅ : Set X) := hIntEmpty
    exact (Set.nonempty_iff_ne_empty).2 h_ne

theorem Topology.interior_diff_subset_interior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  -- Since `A \ B ⊆ A`, apply the monotonicity of `interior`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact interior_mono h_subset

theorem Topology.closure_interior_closure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP2 : Topology.P2 A) :
    closure (interior (closure A)) = closure A := by
  -- First, derive `P3` for `A` from the assumed `P2` property.
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (A := A) hP2
  -- Apply the existing result for `P3` to obtain the desired equality.
  exact
    Topology.closure_interior_closure_eq_closure_of_P3 (A := A) hP3

theorem Topology.P1_inter_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hOpenA : IsOpen A) (hP1B : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  unfold Topology.P1 at *
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` is in the closure of `interior B` by `P1` for `B`
  have h_clB : x ∈ closure (interior B) := hP1B hxB
  -- We prove `x ∈ closure (interior (A ∩ B))` using `mem_closure_iff`
  have : x ∈ closure (interior (A ∩ B)) := by
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Consider the open set `U ∩ A` that still contains `x`
    have hV_open : IsOpen (U ∩ A) := hU_open.inter hOpenA
    have hxV : x ∈ U ∩ A := ⟨hxU, hxA⟩
    -- Since `x ∈ closure (interior B)`, `U ∩ A` meets `interior B`
    have h_nonempty :=
      (mem_closure_iff).1 h_clB (U ∩ A) hV_open hxV
    rcases h_nonempty with ⟨y, ⟨hyU, hyA⟩, hyIntB⟩
    -- Show `y ∈ interior (A ∩ B)`
    have hyIntAB : y ∈ interior (A ∩ B) := by
      -- The open set `A ∩ interior B` contains `y` and is included in `A ∩ B`
      have h_open : IsOpen (A ∩ interior B) := hOpenA.inter isOpen_interior
      have h_subset : (A ∩ interior B) ⊆ A ∩ B := by
        intro z hz; exact ⟨hz.1, interior_subset hz.2⟩
      have hy_in : y ∈ A ∩ interior B := ⟨hyA, hyIntB⟩
      exact (interior_maximal h_subset h_open) hy_in
    exact ⟨y, ⟨hyU, hyIntAB⟩⟩
  exact this



theorem Topology.interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact (subset_closure : interior (closure A) ⊆ closure (interior (closure A))) hx

theorem Topology.P1_inter_isOpen_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1A : Topology.P1 A) (hOpenB : IsOpen B) :
    Topology.P1 (A ∩ B) := by
  -- Expand the definition of `P1`.
  unfold Topology.P1 at *
  -- Take an arbitrary point `x` in `A ∩ B`.
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P1` for `A`, we know `x` is in `closure (interior A)`.
  have h_closure : x ∈ closure (interior A) := hP1A hxA
  -- We aim to prove `x ∈ closure (interior (A ∩ B))`.
  -- Use the neighbourhood‐based characterization of the closure.
  have : x ∈ closure (interior (A ∩ B)) := by
    -- Employ `mem_closure_iff`.
    apply (mem_closure_iff).2
    intro U hU_open hxU
    -- Refine the neighbourhood to stay inside `B`, which is open.
    have hV_open : IsOpen (U ∩ B) := hU_open.inter hOpenB
    have hxV : x ∈ U ∩ B := ⟨hxU, hxB⟩
    -- Since `x ∈ closure (interior A)`, this refined neighbourhood
    -- meets `interior A`.
    have h_nonempty :=
      (mem_closure_iff).1 h_closure (U ∩ B) hV_open hxV
    rcases h_nonempty with ⟨y, ⟨hyU, hyB⟩, hyIntA⟩
    -- Show the intersection point actually lies in `interior (A ∩ B)`.
    have hyIntAB : y ∈ interior (A ∩ B) := by
      -- `interior A` is open, and so is `B`; their intersection is open
      -- and contained in `A ∩ B`.
      have h_open : IsOpen (interior A ∩ B) :=
        isOpen_interior.inter hOpenB
      have h_subset : interior A ∩ B ⊆ A ∩ B := by
        intro z hz
        exact And.intro (interior_subset hz.1) hz.2
      have hy_mem : y ∈ interior A ∩ B := ⟨hyIntA, hyB⟩
      exact interior_maximal h_subset h_open hy_mem
    -- Conclude that `U` meets `interior (A ∩ B)`.
    exact ⟨y, ⟨hyU, hyIntAB⟩⟩
  -- Finish the proof.
  exact this

theorem Topology.P1_of_dense_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense (interior A)) (hAB : interior A ⊆ B) :
    Topology.P1 B := by
  -- We prove `closure (interior B) = univ`, from which `P1 B` is immediate.
  have hIntSubset : interior A ⊆ interior B :=
    interior_maximal hAB isOpen_interior
  -- `interior A` is dense, hence its closure is `univ`.
  have hClosureIntA : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Monotonicity of `closure` gives `closure (interior A) ⊆ closure (interior B)`.
  have hUnivSubset : (Set.univ : Set X) ⊆ closure (interior B) := by
    simpa [hClosureIntA] using (closure_mono hIntSubset)
  -- Trivially, `closure (interior B) ⊆ univ`.
  have hSubsetUniv : closure (interior B) ⊆ (Set.univ : Set X) := by
    intro _ _; simp
  -- Combine the inclusions to obtain the desired equality.
  have hClosureIntB : closure (interior B) = (Set.univ : Set X) :=
    Set.Subset.antisymm hSubsetUniv hUnivSubset
  -- Establish `P1 B`.
  unfold Topology.P1
  intro x hxB
  -- Every point belongs to `univ`, hence to `closure (interior B)`.
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hClosureIntB] using this

theorem Topology.interior_inter_eq_interiors_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ interior B := by
  -- Since `A` and `B` are open, so is `A ∩ B`, and its interior is itself.
  have hInt : interior (A ∩ B) = A ∩ B :=
    (hA.inter hB).interior_eq
  -- The interior of an open set is the set itself.
  have hA_int : interior A = A := hA.interior_eq
  have hB_int : interior B = B := hB.interior_eq
  -- Substitute and simplify.
  simpa [hInt, hA_int, hB_int]

theorem Topology.P2_iUnion_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    Topology.P2 (Set.iUnion A) := by
  -- `P2` holds for every open set `A i`.
  have hP2 : ∀ i, Topology.P2 (A i) := fun i =>
    Topology.P2_of_isOpen (A := A i) (hOpen i)
  -- Use the existing union lemma for `P2`.
  exact Topology.P2_iUnion (A := A) hP2

theorem Topology.interior_closure_idempotent_iter5
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior
      (closure (interior (closure (interior (closure A))))))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior
      (closure (interior (closure (interior (closure A))))))))) =
        interior (closure (interior (closure (interior
          (closure (interior (closure A))))))) := by
          simpa using
            (Topology.interior_closure_idempotent
              (A := interior (closure (interior (closure
                (interior (closure A)))))))
    _ = interior (closure (interior (closure
          (interior (closure A))))) := by
          simpa using
            (Topology.interior_closure_idempotent
              (A := interior (closure (interior (closure A))))
            )
    _ = interior (closure (interior (closure A))) := by
          simpa using
            (Topology.interior_closure_idempotent
              (A := interior (closure A)))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_idempotent (A := A))

theorem Topology.P3_inter_isOpen_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hOpenA : IsOpen A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Expand the definition of `P3`.
  unfold Topology.P3 at *
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P3` for `B`, we get that `x` lies in the interior of `closure B`.
  have hxIntB : x ∈ interior (closure B) := hP3B hxB
  -- The point `x` lies in the open set `A ∩ interior (closure B)`.
  have hxS : x ∈ A ∩ interior (closure B) := And.intro hxA hxIntB
  -- We will show that this open set is contained in `closure (A ∩ B)`.
  have h_subset : (A ∩ interior (closure B)) ⊆ closure (A ∩ B) := by
    intro y hy
    rcases hy with ⟨hyA, hyIntB⟩
    -- `y` belongs to `closure B`.
    have hyClB : y ∈ closure B := interior_subset hyIntB
    -- Prove that `y` is in `closure (A ∩ B)` using the neighbourhood
    -- characterization of the closure.
    have : y ∈ closure (A ∩ B) := by
      apply (mem_closure_iff).2
      intro U hU_open hyU
      -- Refine the neighbourhood to stay inside `A`, which is open.
      have hUA_open : IsOpen (U ∩ A) := hU_open.inter hOpenA
      have hyUA : y ∈ U ∩ A := ⟨hyU, hyA⟩
      -- Because `y ∈ closure B`, the set `(U ∩ A)` meets `B`.
      have h_nonempty : ((U ∩ A) ∩ B).Nonempty := by
        have h := (mem_closure_iff).1 hyClB (U ∩ A) hUA_open hyUA
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
      -- Extract a witness in the required intersection.
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hzB⟩⟩
      exact ⟨z, And.intro hzU (And.intro hzA hzB)⟩
    exact this
  -- The set `A ∩ interior (closure B)` is open.
  have h_open : IsOpen (A ∩ interior (closure B)) :=
    hOpenA.inter isOpen_interior
  -- Use `interior_maximal` to deduce an inclusion into the interior.
  have h_interior :
      (A ∩ interior (closure B)) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal h_subset h_open
  -- Conclude for the original point `x`.
  exact h_interior hxS

theorem Topology.interior_diff_closed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  ext x
  constructor
  · intro hx
    have hxA : x ∈ interior A := by
      -- `A \ B ⊆ A`, hence `interior (A \ B) ⊆ interior A`.
      have h_subset : (A \ B : Set X) ⊆ A := fun y hy => hy.1
      exact (interior_mono h_subset) hx
    have hxNotB : x ∉ B := by
      -- Points in `interior (A \ B)` are certainly not in `B`.
      have hxAB : x ∈ A \ B := interior_subset hx
      exact hxAB.2
    exact And.intro hxA hxNotB
  · intro hx
    rcases hx with ⟨hxIntA, hxNotB⟩
    -- Construct an open neighborhood contained in `A \ B`.
    have hOpenIntA : IsOpen (interior A) := isOpen_interior
    have hOpenComplB : IsOpen (Bᶜ) := hB.isOpen_compl
    have hVopen : IsOpen (interior A ∩ Bᶜ) := hOpenIntA.inter hOpenComplB
    have hxV : x ∈ interior A ∩ Bᶜ := And.intro hxIntA hxNotB
    -- This neighborhood is included in `A \ B`.
    have hVsubset : (interior A ∩ Bᶜ) ⊆ (A \ B) := by
      intro y hy
      have hyA : y ∈ A := interior_subset hy.1
      exact And.intro hyA hy.2
    -- Hence `x` lies in `interior (A \ B)`.
    have hVsubsetInterior : (interior A ∩ Bᶜ) ⊆ interior (A \ B) :=
      interior_maximal hVsubset hVopen
    exact hVsubsetInterior hxV

theorem Topology.P2_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  have h_eq : closure (closure A) = closure A := by
    simpa [closure_closure]
  simpa [h_eq]

theorem Topology.nonempty_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  classical
  intro hP2 hAne
  rcases hAne with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  by_cases hIntEmpty : interior A = (∅ : Set X)
  ·
    -- If `interior A` is empty, we derive a contradiction from `hxInt`.
    have hFalse : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty, interior_empty] using hxInt
    cases hFalse
  ·
    -- Otherwise, `interior A` is non-empty, which is what we wanted.
    have h_ne : interior A ≠ (∅ : Set X) := hIntEmpty
    exact (Set.nonempty_iff_ne_empty).2 h_ne

theorem Topology.iUnion_closure_interiors_subset_closure_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (interior (A i))) ⊆ closure (interior (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hsubset : interior (A i) ⊆ interior (⋃ i, A i) :=
    interior_mono (Set.subset_iUnion A i)
  have hclosure : closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) :=
    closure_mono hsubset
  exact hclosure hx_i

theorem Topology.P2_inter_isOpen_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- Expand the definition of `P2`.
  unfold Topology.P2 at *
  -- Take an arbitrary point `x` in `A ∩ B`.
  intro x hxAB
  rcases hxAB with ⟨hxA, hxB⟩
  -- From `P2` for `B`, obtain the required membership.
  have hxIntB : x ∈ interior (closure (interior B)) := hP2B hxB
  -- Consider the open set `A ∩ interior (closure (interior B))` that contains `x`.
  have hxS : x ∈ A ∩ interior (closure (interior B)) := ⟨hxA, hxIntB⟩
  -- We will show this open set is contained in `closure (interior (A ∩ B))`.
  have h_subset :
      (A ∩ interior (closure (interior B))) ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyA, hyIntB⟩
    -- `y` belongs to the closure of `interior B`.
    have hyClB : y ∈ closure (interior B) := interior_subset hyIntB
    -- Show that `y` lies in the closure of `interior (A ∩ B)`.
    have : y ∈ closure (interior (A ∩ B)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro U hU_open hyU
      -- Refine the neighbourhood to stay inside `A`, which is open.
      have hV_open : IsOpen (U ∩ A) := hU_open.inter hOpenA
      have hyV : y ∈ U ∩ A := ⟨hyU, hyA⟩
      -- Since `y ∈ closure (interior B)`, this refined neighbourhood meets `interior B`.
      have h_nonempty :
          ((U ∩ A) ∩ interior B).Nonempty := by
        have h :=
          (mem_closure_iff).1 hyClB (U ∩ A) hV_open hyV
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h
      rcases h_nonempty with ⟨z, ⟨⟨hzU, hzA⟩, hzIntB⟩⟩
      -- Show that `z ∈ interior (A ∩ B)`.
      have hzIntAB : z ∈ interior (A ∩ B) := by
        -- The set `A ∩ interior B` is an open subset of `A ∩ B` containing `z`.
        have h_open : IsOpen (A ∩ interior B) := hOpenA.inter isOpen_interior
        have h_sub : (A ∩ interior B) ⊆ A ∩ B := by
          intro t ht; exact ⟨ht.1, interior_subset ht.2⟩
        have hz_mem : z ∈ A ∩ interior B := ⟨hzA, hzIntB⟩
        have h_incl : (A ∩ interior B) ⊆ interior (A ∩ B) :=
          interior_maximal h_sub h_open
        exact h_incl hz_mem
      -- Conclude that `U` meets `interior (A ∩ B)`.
      exact ⟨z, ⟨hzU, hzIntAB⟩⟩
    exact this
  -- The set we constructed is open.
  have h_openS : IsOpen (A ∩ interior (closure (interior B))) :=
    hOpenA.inter isOpen_interior
  -- Apply `interior_maximal` to obtain the desired inclusion.
  have h_interior :
      (A ∩ interior (closure (interior B))) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal h_subset h_openS
  -- Finish the proof by applying the inclusion to `x`.
  exact h_interior hxS

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2closure
  -- First, convert `P2` for the closed set `closure A` to `P3`.
  have hClosed : IsClosed (closure A) := isClosed_closure
  have hP3closure : Topology.P3 (closure A) :=
    (Topology.P2_iff_P3_of_isClosed (A := closure A) hClosed).1 hP2closure
  -- Then, transfer the `P3` property from `closure A` to `A`.
  exact Topology.P3_of_P3_closure (A := A) hP3closure

theorem Topology.P2_inter_isOpen_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hOpenB : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  -- Swap the roles of `A` and `B` and reuse the existing left‐hand variant.
  have h := Topology.P2_inter_isOpen_left (A := B) (B := A) hOpenB hP2A
  simpa [Set.inter_comm] using h

theorem Topology.frontier_subset_closure_interior_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    frontier A ⊆ closure (interior A) := by
  intro x hx
  -- From `x ∈ frontier A`, we know `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx.1
  -- Under `P1`, the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
  -- Rewrite the membership using this equality.
  simpa [h_eq] using hx_closure

theorem Topology.P3_inter_isOpen_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hOpenB : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P3_inter_isOpen_left (A := B) (B := A) hOpenB hP3A)

theorem Topology.P2_of_dense_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense (interior A)) (hAB : interior A ⊆ B) :
    Topology.P2 B := by
  unfold Topology.P2
  intro x hxB
  -- Step 1: `interior A ⊆ interior B`
  have hIntSubset : interior A ⊆ interior B :=
    interior_maximal hAB isOpen_interior
  -- Step 2: `closure (interior A) = univ`
  have hClosureA : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Step 3: `closure (interior B) = univ`
  have hClosureB : closure (interior B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    ·
      have h_inc : closure (interior A) ⊆ closure (interior B) :=
        closure_mono hIntSubset
      simpa [hClosureA] using h_inc
  -- Step 4: `interior (closure (interior B)) = univ`
  have hInterior : interior (closure (interior B)) = (Set.univ : Set X) := by
    simpa [hClosureB] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Step 5: Conclude membership
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hInterior] using this

theorem Topology.interior_union_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  simpa using hOpen.interior_eq

theorem Topology.P3_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (closure A) = (Set.univ : Set X)) :
    Topology.P3 A := by
  unfold Topology.P3
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this

theorem Topology.P1_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior A)))) := by
  -- Two useful equalities coming from idempotence of `closure ∘ interior`.
  have h_eq :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using Topology.closure_interior_idempotent (A := A)
  have h_int_eq :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) := by
    simpa using Topology.interior_closure_idempotent (A := interior A)
  -- `P1` is already known for `closure (interior A)`.
  have hP1_base : Topology.P1 (closure (interior A)) :=
    Topology.P1_closure_interior (A := A)
  -- Unfold the definition of `P1` and start the proof.
  unfold Topology.P1 at *
  intro x hx
  -- Transport `x` to the simpler set using `h_eq`.
  have hx_base : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  -- Apply `P1` for `closure (interior A)`.
  have hx_goal_base : x ∈ closure (interior (closure (interior A))) :=
    hP1_base hx_base
  -- Rewrite using `h_int_eq` to match the required target set.
  simpa [h_int_eq] using hx_goal_base

theorem Topology.P1_singleton_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {x : X} :
    Topology.P1 ({x} : Set X) := by
  -- Expand the definition of `P1`.
  unfold Topology.P1
  intro y hy
  -- In a discrete space every set is open; in particular `{x}` is open,
  -- hence its interior is itself.
  have hInt : interior ({x} : Set X) = {x} :=
    (isOpen_discrete ({x} : Set X)).interior_eq
  -- From `y ∈ {x}` we deduce `y ∈ interior {x}` using the equality above.
  have hMemInt : y ∈ interior ({x} : Set X) := by
    simpa [hInt] using hy
  -- Every point of a set is contained in the closure of that set.
  exact (subset_closure hMemInt)

theorem Topology.closure_interior_diff_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  -- First, `interior (A \ B) ⊆ interior A` by monotonicity of `interior`.
  have h₁ : interior (A \ B) ⊆ interior A :=
    Topology.interior_diff_subset_interior_left (A := A) (B := B)
  -- Applying `closure_mono` to `h₁` yields the desired inclusion.
  exact closure_mono h₁

theorem Topology.P_properties_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  simpa using
    (Topology.P_properties_of_isOpen (A := A) hA_open)

theorem Topology.P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {A : Set X} : Topology.P2 A := by
  -- In a discrete topology every set is open.
  have hOpen : IsOpen A := isOpen_discrete _
  -- `P2` holds for every open set.
  exact Topology.P2_of_isOpen (A := A) hOpen

theorem Topology.nonempty_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP3 hAne
  rcases hAne with ⟨x, hxA⟩
  exact ⟨x, hP3 hxA⟩

theorem Topology.P2_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.P2_of_isOpen (A := A ∩ B) hOpen)

theorem Topology.closure_interior_eq_of_closed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = A := by
  -- First, `A` is open because it is closed and satisfies `P3`.
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  -- Hence the interior of `A` is `A` itself.
  have h_int : interior A = A := hA_open.interior_eq
  -- Rewrite `closure (interior A)` using the above equality and use that `A` is closed.
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = A := hA_closed.closure_eq

theorem Topology.P3_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {A : Set X} : Topology.P3 A := by
  have hOpen : IsOpen A := isOpen_discrete _
  exact Topology.P3_of_isOpen (A := A) hOpen

theorem Topology.P1_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {A : Set X} : Topology.P1 A := by
  -- Every subset of a discrete space is open.
  have hOpen : IsOpen A := isOpen_discrete _
  -- All open sets satisfy `P1`.
  exact Topology.P1_of_isOpen (A := A) hOpen

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) :
    interior (Aᶜ) = (∅ : Set X) := by
  classical
  -- We use the characterization `s = ∅ ↔ ∀ x, x ∉ s`.
  apply Set.eq_empty_iff_forall_not_mem.2
  intro x hxInt
  -- Since `A` is dense, every point belongs to `closure A = univ`.
  have hx_closureA : x ∈ closure A := by
    have : x ∈ (Set.univ : Set X) := by simp
    simpa [hDense.closure_eq] using this
  -- The open set `interior (Aᶜ)` contains `x`; by density it meets `A`.
  have h_nonempty :=
    (mem_closure_iff).1 hx_closureA (interior (Aᶜ)) isOpen_interior hxInt
  rcases h_nonempty with ⟨y, hyIntCompl, hyA⟩
  -- But `interior (Aᶜ)` is contained in `Aᶜ`, so `y ∉ A`, contradiction.
  have hyAc : y ∈ Aᶜ := interior_subset hyIntCompl
  exact hyAc hyA

theorem Topology.closure_interior_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    closure (interior A) = A := by
  -- In a discrete topology every set is open, in particular `A`.
  have hOpen : IsOpen A := isOpen_discrete _
  -- Hence `interior A = A`.
  have hInt : interior A = A := hOpen.interior_eq
  -- It suffices to show `closure A = A`.
  suffices closure A = A by
    simpa [hInt] using this
  -- Prove the two inclusions separately.
  apply Set.Subset.antisymm
  · -- Show `closure A ⊆ A`.
    intro x hx
    -- The singleton `{x}` is open in a discrete space.
    have hOpenSingleton : IsOpen ({x} : Set X) := isOpen_discrete _
    -- By definition of the closure, `{x}` meets `A`.
    have hNonempty :
        (({x} : Set X) ∩ A).Nonempty :=
      (mem_closure_iff).1 hx ({x}) hOpenSingleton (by
        -- `x` belongs to the open set `{x}`.
        simp)
    -- Extract a witness from the non-empty intersection.
    rcases hNonempty with ⟨y, ⟨hySingle, hyA⟩⟩
    -- From `y ∈ {x}` we deduce `y = x`.
    have : y = x := by
      simpa [Set.mem_singleton_iff] using hySingle
    -- Conclude `x ∈ A`.
    simpa [this] using hyA
  · -- The reverse inclusion is always true.
    exact subset_closure

theorem Topology.frontier_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP2 : Topology.P2 A) :
    frontier A ⊆ closure (interior A) := by
  intro x hx
  -- From `x ∈ frontier A`, we know `x ∈ closure A`.
  have hx_closure : x ∈ closure A := hx.1
  -- `P2 A` gives the equality `closure (interior A) = closure A`.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P2 (A := A) hP2
  -- Rewrite the membership using this equality.
  simpa [h_eq] using hx_closure

theorem Topology.frontier_subset_closure_interior_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A) :
    frontier A ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_closure : x ∈ closure A := hx.1
  have h_eq :
      closure (interior (closure A)) = closure A :=
    Topology.closure_interior_closure_eq_closure_of_P3 (A := A) hP3
  simpa [h_eq] using hx_closure

theorem Topology.eq_empty_of_P3_and_interior_closure_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} (hP3 : Topology.P3 A)
    (hInt : interior (closure A) = (∅ : Set X)) : A = ∅ := by
  apply Set.Subset.antisymm
  ·
    intro x hxA
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hInt] using this
  ·
    exact Set.empty_subset _

theorem Topology.nonempty_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty →
      (interior (closure (interior A))).Nonempty := by
  intro hP2 hAne
  rcases hAne with ⟨x, hxA⟩
  exact ⟨x, hP2 hxA⟩

theorem Topology.P3_of_dense_interior_alt {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P3 A := by
  -- We already have `P3_of_dense_interior`, use it directly.
  simpa using (Topology.P3_of_dense_interior (A := A) hDense)

theorem Topology.interior_closure_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    interior (closure A) = A := by
  classical
  -- First, prove `closure A = A`.
  have h_closure_eq : closure A = A := by
    apply Set.Subset.antisymm
    · intro x hx_cl
      by_cases hxA : x ∈ A
      · exact hxA
      ·
        -- The singleton `{x}` is open in a discrete space.
        have h_open : IsOpen ({x} : Set X) := isOpen_discrete _
        -- Since `{x}` contains `x` and is open, density in the closure forces
        -- a contradiction if `x ∉ A`.
        have h_nonempty :
            (({x} : Set X) ∩ A).Nonempty :=
          (mem_closure_iff).1 hx_cl ({x}) h_open (by
            simp)
        rcases h_nonempty with ⟨y, ⟨hy_single, hyA⟩⟩
        have h_eq : y = x := by
          simpa [Set.mem_singleton_iff] using hy_single
        have : x ∈ A := by
          simpa [h_eq] using hyA
        exact this
    · exact subset_closure
  -- In a discrete space every set is open, so `interior A = A`.
  have h_interior_eq : interior A = A :=
    (isOpen_discrete _).interior_eq
  -- Rewrite using the two equalities obtained above.
  simpa [h_closure_eq, h_interior_eq]

theorem Topology.frontier_closure_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure A) ⊆ frontier A := by
  intro x hx
  -- `hx` yields both `x ∈ closure (closure A)` and `x ∉ interior (closure A)`.
  have hx_closure : x ∈ closure A := by
    -- Simplify `closure (closure A)` to `closure A`.
    simpa [closure_closure] using hx.1
  have hx_not_intA : x ∉ interior A := by
    intro hx_intA
    -- `interior A ⊆ interior (closure A)`.
    have h_subset : interior A ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (A := A)
    have : x ∈ interior (closure A) := h_subset hx_intA
    exact hx.2 this
  -- Combine the two facts to obtain `x ∈ frontier A`.
  exact And.intro hx_closure hx_not_intA

theorem Topology.P1_iUnion_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    Topology.P1 (Set.iUnion A) := by
  -- Each `A i` is open, hence satisfies `P1`.
  have hP1 : ∀ i, Topology.P1 (A i) :=
    fun i => Topology.P1_of_isOpen (A := A i) (hOpen i)
  -- Apply the existing union lemma for `P1`.
  exact Topology.P1_iUnion (A := A) hP1

theorem Topology.isClosed_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = A) : IsClosed A := by
  -- `closure (interior A)` is always a closed set.
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  -- Rewriting with the given equality yields the desired result.
  simpa [h] using hClosed

theorem Topology.closure_interior_eq_of_subset_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hB : B ⊆ closure (interior A)) :
    closure (interior A) = closure (interior B) := by
  -- We will prove the two inclusions separately and then invoke `subset_antisymm`.
  apply subset_antisymm
  ·
    -- From `A ⊆ B` we get `interior A ⊆ interior B`,
    -- and taking closures preserves inclusions.
    exact closure_mono (interior_mono hAB)
  ·
    -- From `B ⊆ closure (interior A)` we obtain
    -- `interior B ⊆ interior (closure (interior A))`.
    have h₁ : interior B ⊆ interior (closure (interior A)) :=
      interior_mono hB
    -- Taking closures preserves inclusions.
    have h₂ : closure (interior B) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    -- Simplify the right‐hand side using idempotence of `closure ∘ interior`.
    simpa [Topology.closure_interior_idempotent (A := A)] using h₂

theorem Topology.P_properties_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {A : Set X} :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.P1_of_discrete (A := A),
      ⟨Topology.P2_of_discrete (A := A),
        Topology.P3_of_discrete (A := A)⟩⟩

theorem Topology.frontier_eq_empty_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {A : Set X} :
    frontier A = (∅ : Set X) := by
  -- In a discrete topology every set is open, hence its interior is itself.
  have hInt : interior A = A := (isOpen_discrete _).interior_eq
  -- Likewise, every set is closed, so its closure is itself.
  have hClos : closure A = A := by
    have hClosed : IsClosed A := isClosed_discrete _
    simpa using hClosed.closure_eq
  -- Substituting these equalities into the definition of `frontier`
  -- yields the empty set.
  simp [frontier, hInt, hClos, Set.diff_self]

theorem Topology.P1_sUnion_isOpen {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → IsOpen A) → Topology.P1 (⋃₀ 𝒜) := by
  intro hOpen
  -- First, turn the openness assumption into `P1` for every set in `𝒜`.
  have hP1 : ∀ A, A ∈ 𝒜 → Topology.P1 A := by
    intro A hA
    exact Topology.P1_of_isOpen (A := A) (hOpen A hA)
  -- Apply the existing `P1_sUnion` theorem.
  exact Topology.P1_sUnion (X := X) (𝒜 := 𝒜) hP1

theorem Topology.interior_inter_isOpen_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    interior (A ∩ U) = interior A ∩ U := by
  -- First inclusion: `⊆`
  apply Set.Subset.antisymm
  · intro x hx
    have hA : x ∈ interior A := by
      have h_subset : (A ∩ U) ⊆ A := Set.inter_subset_left
      exact (interior_mono h_subset) hx
    have hUx : x ∈ U := by
      have : x ∈ A ∩ U := interior_subset hx
      exact this.2
    exact And.intro hA hUx
  · intro x hx
    rcases hx with ⟨hIntA, hUx⟩
    -- The set `interior A ∩ U` is open
    have h_open : IsOpen (interior A ∩ U) := isOpen_interior.inter hU
    -- and contained in `A ∩ U`
    have h_subset : (interior A ∩ U) ⊆ (A ∩ U) := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- Hence it is contained in the interior of `A ∩ U`
    have h_interior :
        interior A ∩ U ⊆ interior (A ∩ U) :=
      interior_maximal h_subset h_open
    exact h_interior ⟨hIntA, hUx⟩

theorem Topology.P3_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P3 (closure A) := by
  have h_eq : closure (closure A) = closure A := by
    simpa [closure_closure]
  constructor
  · intro h
    simpa [h_eq] using h
  · intro h
    simpa [h_eq] using h

theorem Topology.P1_closure_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (closure A)) ↔ Topology.P1 (closure A) := by
  have h_eq : closure (closure A) = closure A := by
    simpa [closure_closure]
  constructor
  · intro h
    simpa [h_eq] using h
  · intro h
    simpa [h_eq] using h

theorem Topology.interior_closure_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    interior (closure A) = A := by
  calc
    interior (closure A) = interior A := by
      simpa using
        (Topology.interior_closure_eq_interior_of_closed (A := A) hA_closed)
    _ = A := by
      simpa using hA_open.interior_eq

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- First, by monotonicity of `closure`, we have
  -- `closure (interior A) ⊆ closure A`.
  have h : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Since `A` is closed, `closure A = A`; rewrite to conclude.
  simpa [hA.closure_eq] using h

theorem Topology.nonempty_closure_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty ↔ (interior A).Nonempty := by
  constructor
  · intro hClNon
    by_cases hInt : (interior A).Nonempty
    · exact hInt
    ·
      exfalso
      rcases hClNon with ⟨x, hx_cl⟩
      -- If `interior A` is empty, its closure is also empty, contradicting `hx_cl`.
      have hIntEmpty : interior A = (∅ : Set X) := by
        apply Set.eq_empty_iff_forall_not_mem.2
        intro y hy
        have : (interior A).Nonempty := ⟨y, hy⟩
        exact (hInt this).elim
      have hFalse : x ∈ (∅ : Set X) := by
        simpa [hIntEmpty, closure_empty] using hx_cl
      cases hFalse
  · intro hIntNon
    rcases hIntNon with ⟨x, hx_int⟩
    exact ⟨x, subset_closure hx_int⟩

theorem Topology.frontier_eq_empty_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hOpen : IsOpen A) :
    frontier A = (∅ : Set X) := by
  -- `frontier A = closure A \ interior A`; rewrite using the clopen hypotheses.
  simpa [frontier, hClosed.closure_eq, hOpen.interior_eq, Set.diff_self]

theorem Topology.P1_diff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hClosedB : IsClosed B) :
    Topology.P1 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenBc : IsOpen (Bᶜ) := hClosedB.isOpen_compl
  -- Apply the existing intersection lemma with the open complement.
  have h := Topology.P1_inter_isOpen_right (A := A) (B := Bᶜ) hP1A hOpenBc
  -- Rewrite `A ∩ Bᶜ` as `A \ B`.
  simpa [Set.diff_eq] using h

theorem Topology.closed_dense_iff_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Dense A ↔ interior A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- Since `A` is both closed and dense, it is the whole space.
    have h_eq : A = (Set.univ : Set X) :=
      Topology.closed_dense_eq_univ (A := A) hA_closed hDense
    -- Rewriting `interior A` along this equality yields the result.
    simpa [h_eq, interior_univ] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  · intro hInt
    -- From `interior A = univ` we get `A = univ`.
    have h_subset : (Set.univ : Set X) ⊆ A := by
      have : interior A ⊆ A := interior_subset
      simpa [hInt] using this
    have h_eq : A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact h_subset
    -- The whole space is dense, hence so is `A`.
    simpa [h_eq] using (dense_univ : Dense (Set.univ : Set X))

theorem Topology.P3_diff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3A : Topology.P3 A) (hClosedB : IsClosed B) :
    Topology.P3 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenBc : IsOpen (Bᶜ) := hClosedB.isOpen_compl
  -- Apply the existing intersection lemma for `P3` with an open set.
  have h := Topology.P3_inter_isOpen_right (A := A) (B := Bᶜ) hP3A hOpenBc
  -- Rewrite `A ∩ Bᶜ` as `A \ B`.
  simpa [Set.diff_eq] using h

theorem Topology.P2_diff_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hClosedB : IsClosed B) :
    Topology.P2 (A \ B) := by
  -- The complement of a closed set is open.
  have hOpenBc : IsOpen (Bᶜ) := hClosedB.isOpen_compl
  -- Apply the existing intersection lemma for `P2` with an open set.
  have h := Topology.P2_inter_isOpen_right (A := A) (B := Bᶜ) hP2A hOpenBc
  -- Rewrite `A ∩ Bᶜ` as `A \ B`.
  simpa [Set.diff_eq] using h

theorem Topology.interior_diff_closed_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hOpenA : IsOpen A) (hClosedB : IsClosed B) :
    interior (A \ B) = A \ B := by
  simpa [hOpenA.interior_eq] using
    (Topology.interior_diff_closed (A := A) (B := B) hClosedB)

theorem Topology.dense_iff_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ closure (interior (closure A)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
    calc
      closure (interior (closure A))
          = closure (interior (Set.univ : Set X)) := by
              simpa [h_closure]
      _ = closure (Set.univ : Set X) := by
          simpa [interior_univ]
      _ = (Set.univ : Set X) := by
          simpa using closure_univ
  · intro hEq
    -- First, deduce `closure A = Set.univ`.
    have h_closureA_univ : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro x _; simp
      ·
        have h_subset : closure (interior (closure A)) ⊆ closure A :=
          Topology.closure_interior_closure_subset_closure (A := A)
        simpa [hEq] using h_subset
    -- Turn the equality into the `Dense` property.
    have hDense : Dense A := by
      intro x
      have : (x : X) ∈ (Set.univ : Set X) := by simp
      simpa [h_closureA_univ] using this
    exact hDense

theorem Topology.dense_closure_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure A) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    simpa [closure_closure] using hDense.closure_eq
  · intro hEq
    dsimp [Dense]
    simpa [closure_closure, hEq]

theorem Topology.interior_diff_eq_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) = interior A \ closure B := by
  apply Set.Subset.antisymm
  ·
    -- One inclusion is already available.
    exact
      Topology.interior_diff_subset_interior_diff (A := A) (B := B)
  ·
    -- Prove the reverse inclusion.
    intro x hx
    rcases hx with ⟨hxIntA, hxNotClB⟩
    -- Consider the open set `interior A ∩ (closure B)ᶜ` containing `x`.
    have h_open : IsOpen (interior A ∩ (closure B)ᶜ) :=
      isOpen_interior.inter isClosed_closure.isOpen_compl
    have hx_mem : x ∈ interior A ∩ (closure B)ᶜ :=
      And.intro hxIntA hxNotClB
    -- This open set is contained in `A \ B`.
    have h_subset : (interior A ∩ (closure B)ᶜ) ⊆ (A \ B) := by
      intro y hy
      rcases hy with ⟨hyIntA, hyNotClB⟩
      have hyA : y ∈ A := interior_subset hyIntA
      have hyNotB : y ∉ B := by
        intro hyB
        have : y ∈ closure B := subset_closure hyB
        exact hyNotClB this
      exact And.intro hyA hyNotB
    -- Hence, the open set is contained in the interior of `A \ B`.
    have h_interior :
        interior A ∩ (closure B)ᶜ ⊆ interior (A \ B) :=
      interior_maximal h_subset h_open
    -- Conclude that `x` is in the interior of `A \ B`.
    exact h_interior hx_mem

theorem Topology.P1_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.P1_of_isOpen (A := A ∩ B) hOpen)

theorem Topology.P3_of_dense_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense A) (hAB : A ⊆ B) : Topology.P3 B := by
  -- Unfold the definition of `P3`.
  unfold Topology.P3
  intro x hxB
  -- Since `A` is dense, its closure is the whole space.
  have hClosureA : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Using monotonicity of `closure`, deduce that `closure B` is also the whole space.
  have hSubset : closure A ⊆ closure B := closure_mono hAB
  have hClosureB : closure B = (Set.univ : Set X) := by
    -- Show the two inclusions needed for set equality.
    apply Set.Subset.antisymm
    ·
      -- `closure B ⊆ univ` is trivial.
      intro _ _; simp
    ·
      -- `univ ⊆ closure B` follows from `closure A = univ` and `closure A ⊆ closure B`.
      simpa [hClosureA] using hSubset
  -- Consequently, the interior of `closure B` is also the whole space.
  have hInteriorB : interior (closure B) = (Set.univ : Set X) := by
    simpa [hClosureB] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Any point of `B` lies in `univ`, hence in `interior (closure B)`.
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hInteriorB] using this

theorem Topology.frontier_inter_subset_union_frontier
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Decompose the hypothesis `hx : x ∈ frontier (A ∩ B)`
  rcases hx with ⟨hClAB, hNotIntAB⟩
  -- `x` is in the closures of both `A` and `B`
  have hClA : x ∈ closure A :=
    (Topology.closure_inter_subset_inter_closure
        (A := A) (B := B)) hClAB |>.1
  have hClB : x ∈ closure B :=
    (Topology.closure_inter_subset_inter_closure
        (A := A) (B := B)) hClAB |>.2
  -- Case distinction on whether `x ∈ interior A`
  by_cases hIntA : x ∈ interior A
  · -- If `x ∈ interior A`, show that `x ∈ frontier B`
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      -- `x` would then lie in `interior (A ∩ B)`, contradicting `hNotIntAB`
      have hOpen : IsOpen (interior A ∩ interior B) :=
        isOpen_interior.inter isOpen_interior
      have hSub : (interior A ∩ interior B) ⊆ (A ∩ B) := by
        intro y hy
        exact ⟨interior_subset hy.1, interior_subset hy.2⟩
      have hIntSub :
          (interior A ∩ interior B) ⊆ interior (A ∩ B) :=
        interior_maximal hSub hOpen
      have : x ∈ interior (A ∩ B) := hIntSub ⟨hIntA, hIntB⟩
      exact hNotIntAB this
    -- Assemble the frontier membership for `B`
    have hFrontB : x ∈ frontier B := And.intro hClB hNotIntB
    exact Or.inr hFrontB
  · -- If `x ∉ interior A`, then `x ∈ frontier A`
    have hNotIntA : x ∉ interior A := hIntA
    have hFrontA : x ∈ frontier A := And.intro hClA hNotIntA
    exact Or.inl hFrontA

theorem Topology.closure_interior_interior_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.interior_closure_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  -- Since `closure` distributes over unions, rewrite and finish.
  have h : closure (A ∪ B) = closure A ∪ closure B := by
    simpa using closure_union (s := A) (t := B)
  simpa using congrArg interior h

theorem Topology.closure_interior_diff_subset_closure_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) \ interior B := by
  classical
  intro x hx
  -- First, `x` lies in `closure (interior A)` because
  -- `interior (A \ B) ⊆ interior A`.
  have hx_closureA : x ∈ closure (interior A) := by
    have h_subset : interior (A \ B) ⊆ interior A :=
      Topology.interior_diff_subset_interior_left (A := A) (B := B)
    exact (closure_mono h_subset) hx
  -- Next, we show `x ∉ interior B`; otherwise we obtain a contradiction.
  have hx_not_intB : x ∉ interior B := by
    intro hxIntB
    -- The open set `interior B` contains `x`.
    have h_nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases h_nonempty with ⟨y, hyIntB, hyIntDiff⟩
    -- From `y ∈ interior (A \ B)` we know `y ∈ A \ B`, so `y ∉ B`.
    have hy_notB : y ∉ B := (interior_subset hyIntDiff).2
    -- But `y ∈ interior B` implies `y ∈ B`, contradiction.
    exact hy_notB (interior_subset hyIntB)
  -- Assemble the required membership in the set difference.
  exact And.intro hx_closureA hx_not_intB

theorem Topology.P2_sUnion_isOpen {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → IsOpen A) → Topology.P2 (⋃₀ 𝒜) := by
  intro hOpen
  -- First, upgrade the openness assumption to `P2` for every set in `𝒜`.
  have hP2 : ∀ A, A ∈ 𝒜 → Topology.P2 A := by
    intro A hA
    exact Topology.P2_of_isOpen (A := A) (hOpen A hA)
  -- Apply the existing `P2_sUnion` lemma.
  exact Topology.P2_sUnion (X := X) (𝒜 := 𝒜) hP2

theorem Topology.P3_closure_interior_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 (closure (interior (closure (interior A)))) ↔
      Topology.P3 (closure (interior A)) := by
  -- The core equality coming from idempotence of `closure ∘ interior`.
  have hEq :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_idempotent (A := A)
  constructor
  · intro hP3
    simpa [hEq] using hP3
  · intro hP3
    simpa [hEq] using hP3

theorem Topology.frontier_union_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  rcases hx with ⟨hClUnion, hNotIntUnion⟩
  -- `x` lies in either `closure A` or `closure B`
  have hCl : x ∈ closure A ∪ closure B := by
    simpa [closure_union] using hClUnion
  -- The interiors satisfy `interior A ∪ interior B ⊆ interior (A ∪ B)`
  have hIntSubset : interior A ∪ interior B ⊆ interior (A ∪ B) := by
    intro y hy
    cases hy with
    | inl hIntA =>
        exact
          (interior_mono (Set.subset_union_left : A ⊆ A ∪ B)) hIntA
    | inr hIntB =>
        exact
          (interior_mono (Set.subset_union_right : B ⊆ A ∪ B)) hIntB
  -- Case analysis on which closure contains `x`
  cases hCl with
  | inl hClA =>
      have hNotIntA : x ∉ interior A := by
        intro hIntA
        have : x ∈ interior (A ∪ B) := hIntSubset (Or.inl hIntA)
        exact hNotIntUnion this
      exact Or.inl ⟨hClA, hNotIntA⟩
  | inr hClB =>
      have hNotIntB : x ∉ interior B := by
        intro hIntB
        have : x ∈ interior (A ∪ B) := hIntSubset (Or.inr hIntB)
        exact hNotIntUnion this
      exact Or.inr ⟨hClB, hNotIntB⟩

theorem Topology.frontier_eq_closure_diff_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    frontier A = closure A \ A := by
  simpa [frontier, hA.interior_eq]

theorem Topology.closure_interior_union_eq_closure_union_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (A ∪ B) := by
  have hUnion : IsOpen (A ∪ B) := hA.union hB
  simpa using
    (Topology.closure_interior_eq_closure_of_isOpen (A := A ∪ B) hUnion)

theorem Topology.isOpen_closure_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) : IsOpen (closure A) := by
  have h_eq : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  simpa [h_eq] using isOpen_univ

theorem Topology.inter_interior_subset_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∩ interior B ⊆ interior (A ∩ B) := by
  intro x hx
  -- The set `interior A ∩ interior B` is open.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- It is contained in `A ∩ B`.
  have hSubset : interior A ∩ interior B ⊆ A ∩ B := by
    intro y hy
    exact ⟨interior_subset hy.1, interior_subset hy.2⟩
  -- By the maximality of the interior, it is contained in `interior (A ∩ B)`.
  have hInterior : interior A ∩ interior B ⊆ interior (A ∩ B) :=
    interior_maximal hSubset hOpen
  exact hInterior hx

theorem Topology.P3_inter_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.P3_of_isOpen (A := A ∩ B) hOpen)

theorem Topology.P_properties_of_closed_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hDense : Dense A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- A closed and dense set must coincide with the whole space.
  have hEq : A = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (A := A) hClosed hDense
  -- All three properties hold for `Set.univ`; transport them along the equality.
  simpa [hEq] using (Topology.P_properties_univ (X := X))

theorem Topology.closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (interior (Set.iInter A)) ⊆ (Set.iInter fun i => closure (interior (A i))) := by
  intro x hx
  -- For every index `i`, show that `x` lies in `closure (interior (A i))`.
  have hx_i : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `interior` is monotone, and `⋂ i, A i` is contained in each `A i`.
    have h_subset : interior (Set.iInter A) ⊆ interior (A i) :=
      interior_mono (Set.iInter_subset A i)
    -- Taking closures preserves inclusions.
    have h_closure : closure (interior (Set.iInter A)) ⊆
        closure (interior (A i)) := closure_mono h_subset
    exact h_closure hx
  -- Assemble the memberships into the required intersection.
  exact Set.mem_iInter.2 hx_i

theorem Topology.frontier_inter_interior_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} : frontier A ∩ interior A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hFront, hInt⟩
    -- From `x ∈ frontier A` we know `x ∉ interior A`,
    -- contradicting `x ∈ interior A`.
    exact (hFront.2 hInt).elim
  · exact Set.empty_subset _

theorem Topology.dense_interior_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    simpa using hDense.closure_eq
  · intro hEq
    -- Build the `Dense` property from the closure equality.
    have hDense : Dense (interior A) := by
      intro x
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [hEq] using this
    exact hDense

theorem Topology.frontier_eq_self_diff_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    frontier A = A \ interior A := by
  simpa [frontier, hA.closure_eq]

theorem Topology.interior_union_eq_union_interior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = interior A ∪ interior B := by
  -- For open sets, the interior coincides with the set itself.
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  -- Likewise, `A ∪ B` is open, so its interior is itself.
  have hIntUnion : interior (A ∪ B) = A ∪ B :=
    Topology.interior_union_eq_of_isOpen (A := A) (B := B) hA hB
  -- Rewrite each interior using the equalities above and simplify.
  simpa [hIntA, hIntB, hIntUnion]

theorem Topology.closure_interior_closure_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    closure (interior (closure A)) = A := by
  -- In a discrete topology every set is closed, hence `closure A = A`.
  have hClosure : closure A = (A : Set X) := by
    have hClosed : IsClosed A := isClosed_discrete _
    simpa using hClosed.closure_eq
  -- Rewriting with `hClosure` reduces the statement to the known lemma.
  calc
    closure (interior (closure A)) = closure (interior A) := by
      simpa [hClosure]
    _ = A := by
      simpa using Topology.closure_interior_eq_self_of_discrete (A := A)

theorem Topology.frontier_inter_interior_closure_eq_diff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ∩ interior (closure A) = interior (closure A) \ interior A := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hFront, hIntClos⟩
    -- `hFront` gives both `x ∈ closure A` and `x ∉ interior A`;
    -- `hIntClos` is `x ∈ interior (closure A)`.
    exact ⟨hIntClos, hFront.2⟩
  · intro hx
    rcases hx with ⟨hIntClos, hNotIntA⟩
    -- From `x ∈ interior (closure A)` we deduce `x ∈ closure A`.
    have hClA : x ∈ closure A := interior_subset hIntClos
    -- Assemble the frontier membership.
    have hFront : x ∈ frontier A := And.intro hClA hNotIntA
    exact And.intro hFront hIntClos



theorem Topology.interior_closure_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  exact interior_subset

theorem Topology.frontier_subset_closure_interior_of_subset_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP1B : Topology.P1 B) :
    frontier A ⊆ closure (interior B) := by
  intro x hx
  -- From `x ∈ frontier A`, obtain `x ∈ closure A`.
  have hx_clA : x ∈ closure A := hx.1
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_cl_subset : closure A ⊆ closure B := closure_mono hAB
  have hx_clB : x ∈ closure B := h_cl_subset hx_clA
  -- `P1 B` gives `B ⊆ closure (interior B)`.
  have hB_subset : B ⊆ closure (interior B) := hP1B
  -- Taking closures preserves inclusions; simplify `closure (closure _)`.
  have h_clB_subset : closure B ⊆ closure (interior B) := by
    simpa [closure_closure] using closure_mono hB_subset
  -- Combine the inclusions to conclude the desired membership.
  exact h_clB_subset hx_clB

theorem Topology.frontier_subset_closure_interior_of_subset_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    frontier A ⊆ closure (interior B) := by
  intro x hx
  -- From `x ∈ frontier A`, we get `x ∈ closure A`.
  have hx_clA : x ∈ closure A := hx.1
  -- Using the inclusion `A ⊆ B`, deduce `x ∈ closure B`.
  have hx_clB : x ∈ closure B := (closure_mono hAB) hx_clA
  -- For a set satisfying `P2`, its two closures coincide.
  have h_eq : closure (interior B) = closure B :=
    Topology.closure_interior_eq_closure_of_P2 (A := B) hP2B
  -- Rewrite and conclude.
  simpa [h_eq] using hx_clB

theorem Topology.P3_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) : Topology.P3 A := by
  -- We already have all three properties for a closed, dense set.
  have h := Topology.P_properties_of_closed_dense (A := A) hClosed hDense
  -- Extract the `P3` component.
  exact h.right.right

theorem Topology.P1_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  -- Unfold the definition of `P1`.
  unfold Topology.P1
  -- Take an arbitrary point `x ∈ A`.
  intro x hxA
  -- Since `closure (interior A) = univ`, every point lies in it.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  -- Rewrite using the provided equality to get the desired membership.
  simpa [h] using this

theorem Topology.dense_iff_eq_univ_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Dense A ↔ A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- In a discrete space every set is closed, so its closure is itself.
    have hClosed : IsClosed A := isClosed_discrete _
    have hClosureSelf : closure A = A := hClosed.closure_eq
    -- Density gives `closure A = univ`; rewrite to obtain the desired equality.
    have hClosureUniv : closure A = (Set.univ : Set X) := hDense.closure_eq
    simpa [hClosureSelf] using hClosureUniv
  · intro hEq
    -- If `A = univ`, it is trivially dense.
    simpa [hEq] using (dense_univ : Dense (Set.univ : Set X))

theorem Topology.interior_iInter_subset_iInter_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (Set.iInter A) ⊆ Set.iInter (fun i => interior (A i)) := by
  intro x hx
  -- For every index `i`, derive `x ∈ interior (A i)`.
  have hxi : ∀ i, x ∈ interior (A i) := by
    intro i
    -- `⋂ i, A i ⊆ A i`
    have h_subset : (Set.iInter A) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` yields the desired inclusion.
    have h_mono : interior (Set.iInter A) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_mono hx
  -- Assemble the memberships into the required intersection.
  exact Set.mem_iInter.2 hxi

theorem Topology.closure_iInter_subset_iInter_closure {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (Set.iInter A) ⊆ Set.iInter (fun i => closure (A i)) := by
  intro x hx
  -- Show that `x` lies in the closure of every `A i`.
  have hx_i : ∀ i, x ∈ closure (A i) := by
    intro i
    have h_subset : (Set.iInter A) ⊆ A i := Set.iInter_subset A i
    exact (closure_mono h_subset) hx
  exact Set.mem_iInter.2 hx_i

theorem Topology.frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = closure A ∩ closure (Aᶜ) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx_cl, hx_not_int⟩
    -- `x ∉ interior A` gives membership in the complement of `interior A`
    have h_mem_compl : x ∈ (interior A)ᶜ := by
      simpa using hx_not_int
    -- Rewrite using `closure_compl` to obtain membership in `closure (Aᶜ)`
    have hx_cl_compl : x ∈ closure (Aᶜ) := by
      simpa [closure_compl] using h_mem_compl
    exact And.intro hx_cl hx_cl_compl
  · intro hx
    rcases hx with ⟨hx_clA, hx_clAc⟩
    -- From `x ∈ closure (Aᶜ)` derive `x ∉ interior A`
    have hx_not_int : x ∉ interior A := by
      have h_mem_compl : x ∈ (interior A)ᶜ := by
        simpa [closure_compl] using hx_clAc
      simpa using h_mem_compl
    exact And.intro hx_clA hx_not_int

theorem Topology.closed_dense_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hDenseInt : Dense (interior A)) :
    A = (Set.univ : Set X) := by
  -- The density of `interior A` implies `closure A = univ`.
  have hClosure : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDenseInt
  -- Since `A` is closed, `closure A = A`; combine the equalities.
  simpa [hClosed.closure_eq] using hClosure

theorem Topology.interior_inter_closure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    -- `closure A ∩ closure B ⊆ closure A`
    have h_sub : (closure A ∩ closure B : Set X) ⊆ closure A := by
      intro y hy; exact hy.1
    exact (interior_mono h_sub) hx
  have hxB : x ∈ interior (closure B) := by
    -- `closure A ∩ closure B ⊆ closure B`
    have h_sub : (closure A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact (interior_mono h_sub) hx
  exact And.intro hxA hxB

theorem Topology.closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x ∈ closure (interior A)`
  have hxA : x ∈ closure (interior A) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior A := by
      intro y hy; exact hy.1
    exact (closure_mono h_subset) hx
  -- Show `x ∈ closure (interior B)`
  have hxB : x ∈ closure (interior B) := by
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy; exact hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hxA hxB

theorem Topology.interior_iUnion_eq_of_isOpen {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} (hOpen : ∀ i, IsOpen (A i)) :
    interior (Set.iUnion A) = Set.iUnion A := by
  have hOpenUnion : IsOpen (Set.iUnion A) := isOpen_iUnion hOpen
  simpa using hOpenUnion.interior_eq

theorem Topology.isClosed_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure (s := interior A))

theorem Topology.closure_diff_subset_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  exact closure_mono (Set.diff_subset : (A \ B) ⊆ A)

theorem Topology.iUnion_closure_subset_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_subset : closure (A i) ⊆ closure (⋃ i, A i) :=
    closure_mono (Set.subset_iUnion A i)
  exact h_subset hx_i



theorem Topology.frontier_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  -- First, upgrade the membership to `frontier A` using the existing lemma.
  have hFrontA : x ∈ frontier A :=
    (Topology.frontier_interior_subset_frontier (A := A)) hx
  -- Points in the frontier of `A` lie in `closure A`.
  exact hFrontA.1

theorem Topology.frontier_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    frontier A ⊆ closure B := by
  intro x hx
  -- From `x ∈ frontier A`, we know `x ∈ closure A`.
  have hxClA : x ∈ closure A := hx.1
  -- Monotonicity of `closure` under the inclusion `A ⊆ B`.
  have hIncl : closure A ⊆ closure B := closure_mono hAB
  exact hIncl hxClA

theorem Topology.frontier_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : frontier A ⊆ A := by
  intro x hx
  have hx_cl : x ∈ closure A := hx.1
  simpa [hA_closed.closure_eq] using hx_cl

theorem Topology.frontier_closure_eq_closure_diff_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure A) = closure A \ interior (closure A) := by
  simpa [frontier, closure_closure]

theorem Topology.interior_subset_closure_interior_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior A ⊆ closure (interior B) := by
  intro x hx
  -- Step 1: use monotonicity of `interior` under `hAB`
  have hx_intB : x ∈ interior B := (interior_mono hAB) hx
  -- Step 2: every set is contained in the closure of itself
  exact (subset_closure : interior B ⊆ closure (interior B)) hx_intB

theorem Topology.P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = (Set.univ : Set X)) : Topology.P3 A := by
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [h] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  exact Topology.P3_of_interior_closure_eq_univ (A := A) hInt

theorem Topology.frontier_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure A := by
  intro x hx
  exact hx.1

theorem Topology.frontier_interior_eq_closure_interior_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior A) = closure (interior A) \ interior A := by
  simp [frontier, interior_interior]



theorem Topology.closure_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem Topology.frontier_interior_subset_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior A) ⊆ closure A \ interior A := by
  intro x hx
  -- First, upgrade `hx : x ∈ frontier (interior A)` to a membership in `frontier A`.
  have hFrontA : x ∈ frontier A :=
    (Topology.frontier_interior_subset_frontier (A := A)) hx
  -- Decompose `hFrontA` into the two required components.
  exact And.intro hFrontA.1 hFrontA.2

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `x` lies in `closure A` because `A ∩ interior B ⊆ A`.
  have hxA : x ∈ closure A := by
    have h_subset : (A ∩ interior B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono h_subset) hx
  -- `x` lies in `closure B` because `interior B ⊆ B`.
  have hxB : x ∈ closure B := by
    have h_subset : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_diff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  -- Since `A \ B ⊆ A`, apply monotonicity of `interior ∘ closure`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  exact
    Topology.interior_closure_mono
      (A := A \ B) (B := A) h_subset

theorem Topology.closure_inter_eq_self_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  simpa using (hA.inter hB).closure_eq

theorem Topology.closure_interior_closure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  -- An open set satisfies `P3`.
  have hP3 : Topology.P3 A := Topology.P3_of_isOpen (A := A) hA
  -- Apply the existing lemma that turns `P3` into the desired equality.
  simpa using
    (Topology.closure_interior_closure_eq_closure_of_P3 (A := A) hP3)



theorem Topology.interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`.
    have hsubset : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    -- Hence `interior A` must be empty.
    have hSubEmpty : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ interior (closure (interior A)) := hsubset hx
      simpa [h] using this
    exact Set.Subset.antisymm hSubEmpty (Set.empty_subset _)
  · intro h
    -- Rewrite and simplify using `h`.
    simpa [h, closure_empty, interior_empty]



theorem Topology.closure_interior_subset_closure_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  have h_sub : interior A ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
  exact closure_mono h_sub

theorem Topology.closure_interior_eq_univ_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) ↔
      interior (closure (interior A)) = (Set.univ : Set X) := by
  constructor
  · intro h
    have : interior (closure (interior A)) =
        interior (Set.univ : Set X) := by
      simpa [h]
    simpa [interior_univ] using this
  · intro h
    -- `interior S ⊆ S` for any set `S`
    have h_subset : interior (closure (interior A)) ⊆
        closure (interior A) := interior_subset
    -- Using `h`, this gives `univ ⊆ closure (interior A)`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [h]
        using (show interior (closure (interior A)) ⊆ closure (interior A) from h_subset)
    -- The reverse inclusion is trivial.
    have h_subset_univ : closure (interior A) ⊆ (Set.univ : Set X) := by
      intro _ _; simp
    exact Set.Subset.antisymm h_subset_univ h_univ_subset

theorem Topology.frontier_subset_closure_interior_iff_closure_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure (interior A) ↔ closure (interior A) = closure A := by
  constructor
  · intro hSub
    -- We already have `closure (interior A) ⊆ closure A`.
    apply Set.Subset.antisymm
    ·
      exact closure_mono (interior_subset : interior A ⊆ A)
    ·
      intro x hxClosA
      by_cases hxInt : x ∈ interior A
      ·
        -- Case `x ∈ interior A`
        exact subset_closure hxInt
      ·
        -- Case `x ∉ interior A`, so `x ∈ frontier A`
        have hxFront : x ∈ frontier A := by
          exact And.intro hxClosA hxInt
        exact hSub hxFront
  · intro hEq
    -- Rewrite membership using the equality of closures.
    intro x hxFront
    have : x ∈ closure A := hxFront.1
    simpa [hEq] using this

theorem Topology.closure_eq_union_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = A ∪ frontier A := by
  apply Set.Subset.antisymm
  · intro x hx_cl
    by_cases hA : x ∈ A
    · exact Or.inl hA
    ·
      have hx_not_int : x ∉ interior A := by
        intro hxInt
        have : x ∈ A := interior_subset hxInt
        exact hA this
      have hx_frontier : x ∈ frontier A := And.intro hx_cl hx_not_int
      exact Or.inr hx_frontier
  · intro x hx_union
    cases hx_union with
    | inl hxA =>
        exact subset_closure hxA
    | inr hxFrontier =>
        exact hxFrontier.1

theorem Topology.interior_closure_interior_inter_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`.
  have h_subset_A : interior (A ∩ B) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
  have h_subset_B : interior (A ∩ B) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
  -- Taking closures preserves these inclusions.
  have h_closure_A :
      closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono h_subset_A
  have h_closure_B :
      closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono h_subset_B
  -- Applying `interior_mono` gives the desired inclusions on interiors of closures.
  have hx_A : x ∈ interior (closure (interior A)) :=
    (interior_mono h_closure_A) hx
  have hx_B : x ∈ interior (closure (interior B)) :=
    (interior_mono h_closure_B) hx
  exact And.intro hx_A hx_B



theorem Topology.interior_inter_subset_interior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A := by
  intro x hx
  -- Since `A ∩ B ⊆ A`, apply `interior_mono` to obtain the desired inclusion.
  have h_subset : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
  exact (interior_mono h_subset) hx

theorem Topology.closure_interior_inter_eq_closure_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∩ B)) = closure (A ∩ B) := by
  -- Since `A` and `B` are open, so is `A ∩ B`, and its interior is itself.
  have hInt : interior (A ∩ B) = A ∩ B := (hA.inter hB).interior_eq
  -- Rewriting with `hInt` yields the desired equality.
  simpa [hInt]

theorem Topology.dense_iff_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact hDense.closure_eq
  · intro hEq
    have hDense : Dense A := by
      intro x
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [hEq] using this
    exact hDense

theorem Topology.P3_sUnion_isOpen {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    (∀ A, A ∈ 𝒜 → IsOpen A) → Topology.P3 (⋃₀ 𝒜) := by
  intro hOpen
  -- Upgrade the openness assumption to `P3` for every set in `𝒜`.
  have hP3 : ∀ A, A ∈ 𝒜 → Topology.P3 A := by
    intro A hA
    exact Topology.P3_of_isOpen (A := A) (hOpen A hA)
  -- Apply the existing `P3_sUnion` lemma.
  exact Topology.P3_sUnion (X := X) (𝒜 := 𝒜) hP3

theorem Topology.P1_iff_frontier_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ frontier A ⊆ closure (interior A) := by
  -- First equivalence: `P1 A ↔ closure (interior A) = closure A`.
  have h₁ : Topology.P1 A ↔ closure (interior A) = closure A :=
    Topology.P1_iff_closure_interior_eq_closure (A := A)
  -- Second equivalence: `closure (interior A) = closure A ↔ frontier A ⊆ closure (interior A)`.
  have h₂ : closure (interior A) = closure A ↔ frontier A ⊆ closure (interior A) :=
    (Topology.frontier_subset_closure_interior_iff_closure_interior_eq_closure (A := A)).symm
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem Topology.P1_iff_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : Topology.P1 A ↔ A ⊆ closure (interior A) := by
  rfl

theorem Topology.frontier_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- `hx.1` witnesses that `x` lies in the closure of `A ∩ B`.
  have h := (Topology.closure_inter_subset_inter_closure
      (A := A) (B := B)) hx.1
  exact h



theorem Topology.interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    interior (closure A) ⊆ closure (interior A) := by
  intro x hx
  -- First, note that `x ∈ closure A` because `interior (closure A) ⊆ closure A`.
  have hx_closureA : x ∈ closure A := interior_subset hx
  -- Under `P1`, the two closures coincide.
  have h_eq : closure (interior A) = closure A :=
    Topology.closure_interior_eq_closure_of_P1 (A := A) hP1
  -- Rewrite to obtain the desired membership.
  simpa [h_eq] using hx_closureA

theorem Topology.frontier_isClosed {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (frontier A) := by
  -- `closure A` and `closure (Aᶜ)` are both closed, so their intersection is closed.
  have hClosed : IsClosed (closure A ∩ closure (Aᶜ)) :=
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure (Aᶜ)))
  -- Rewrite the intersection as the frontier.
  simpa [Topology.frontier_eq_closure_inter_closure_compl (A := A)] using hClosed

theorem Topology.closure_frontier_eq_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) = frontier A := by
  have hClosed : IsClosed (frontier A) :=
    Topology.frontier_isClosed (A := A)
  simpa using hClosed.closure_eq

theorem Topology.frontier_univ {X : Type*} [TopologicalSpace X] :
    frontier (Set.univ : Set X) = (∅ : Set X) := by
  simp [frontier]

theorem Topology.frontier_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A ⊆ closure (Aᶜ) := by
  intro x hx
  have h : x ∈ closure A ∩ closure (Aᶜ) := by
    simpa [Topology.frontier_eq_closure_inter_closure_compl (A := A)] using hx
  exact h.2



theorem Topology.frontier_closure_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense A) :
    frontier (closure A) = (∅ : Set X) := by
  -- `A` is dense, so its closure is the whole space.
  have hCl : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Consequently, the interior of this closure is also the whole space.
  have hInt : interior (closure A) = (Set.univ : Set X) := by
    simpa [hCl] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Rewrite the frontier of `closure A` using an existing lemma.
  have hFront :
      frontier (closure A) =
        closure A \ interior (closure A) :=
    Topology.frontier_closure_eq_closure_diff_interior_closure (A := A)
  -- Combine the above equalities and simplify.
  calc
    frontier (closure A) =
        closure A \ interior (closure A) := hFront
    _ = (Set.univ : Set X) \ (Set.univ : Set X) := by
      simpa [hCl, hInt]
    _ = (∅ : Set X) := by
      simp

theorem Topology.frontier_empty {X : Type*} [TopologicalSpace X] :
    frontier (∅ : Set X) = (∅ : Set X) := by
  simp [frontier]

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  have hsubset : interior (A i) ⊆ interior (⋃ i, A i) :=
    interior_mono (Set.subset_iUnion A i)
  exact hsubset hxInt

theorem Topology.frontier_subset_closure_interior_of_subset_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP3B : Topology.P3 B) :
    frontier A ⊆ closure (interior (closure B)) := by
  intro x hx
  -- `x` lies in the closure of `A`.
  have hx_clA : x ∈ closure A := hx.1
  -- By monotonicity of `closure`, it also lies in the closure of `B`.
  have hx_clB : x ∈ closure B := (closure_mono hAB) hx_clA
  -- `P3 B` gives `B ⊆ interior (closure B)`, hence
  -- `closure B ⊆ closure (interior (closure B))`.
  have h_subset : closure B ⊆ closure (interior (closure B)) :=
    closure_mono (hP3B : B ⊆ interior (closure B))
  exact h_subset hx_clB

theorem Topology.closure_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∪ frontier A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl h_cl_int =>
        -- `closure (interior A)` is contained in `closure A`
        have h_sub : closure (interior A) ⊆ closure A :=
          closure_mono (interior_subset : interior A ⊆ A)
        exact h_sub h_cl_int
    | inr h_front =>
        -- Points in the frontier of `A` lie in `closure A`
        exact h_front.1
  · intro hx_clA
    by_cases h_intA : x ∈ interior A
    · -- If `x ∈ interior A`, then it is in `closure (interior A)`
      have : x ∈ closure (interior A) := subset_closure h_intA
      exact Or.inl this
    · -- Otherwise, `x` belongs to the frontier of `A`
      have : x ∈ frontier A := And.intro hx_clA h_intA
      exact Or.inr this

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_clA, hx_intB⟩
  -- We show `x ∈ closure (A ∩ B)` using the neighbourhood characterization.
  apply (mem_closure_iff).2
  intro U hU_open hxU
  -- Refine the neighbourhood to stay inside `B`.
  have hV_open : IsOpen (U ∩ interior B) := hU_open.inter isOpen_interior
  have hxV : x ∈ U ∩ interior B := ⟨hxU, hx_intB⟩
  -- Since `x ∈ closure A`, this refined neighbourhood meets `A`.
  have h_nonempty : ((U ∩ interior B) ∩ A).Nonempty := by
    have := (mem_closure_iff).1 hx_clA (U ∩ interior B) hV_open hxV
    simpa [Set.inter_left_comm, Set.inter_assoc] using this
  -- Extract a witness in the required intersection.
  rcases h_nonempty with ⟨y, ⟨⟨hyU, hyIntB⟩, hyA⟩⟩
  have hyB : y ∈ B := interior_subset hyIntB
  exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = s := by
  simpa using (compl_compl s)

theorem Topology.frontier_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  -- Express both frontiers via closures and complements.
  have h₁ : frontier (Aᶜ) = closure (Aᶜ) ∩ closure A := by
    simpa [Set.compl_compl] using
      (Topology.frontier_eq_closure_inter_closure_compl (A := Aᶜ))
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) := by
    simpa using
      (Topology.frontier_eq_closure_inter_closure_compl (A := A))
  -- The right‐hand sides are equal up to commutativity of `∩`.
  simpa [h₁, h₂, Set.inter_comm]

theorem Topology.frontier_compl_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  simpa [frontier_eq_closure_inter_closure_compl, Set.inter_comm, Set.compl_compl]

theorem Topology.interior_eq_diff_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A \ frontier A := by
  ext x
  constructor
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hxNotFrontier : x ∉ frontier A := by
      intro hxFront
      -- `hxFront.2` asserts `x ∉ interior A`, contradicting `hxInt`.
      exact hxFront.2 hxInt
    exact And.intro hxA hxNotFrontier
  · intro hx
    rcases hx with ⟨hxA, hxNotFrontier⟩
    by_cases hxInt : x ∈ interior A
    · exact hxInt
    ·
      -- From `x ∈ A` we get `x ∈ closure A`.
      have hxClos : x ∈ closure A := subset_closure hxA
      -- Together with `hxInt : x ∉ interior A`, this places `x` in the frontier,
      -- contradicting `hxNotFrontier`.
      have hxFrontier : x ∈ frontier A := And.intro hxClos hxInt
      exact False.elim (hxNotFrontier hxFrontier)

theorem Topology.frontier_diff_subset_union_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    frontier (A \ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Rewrite the frontier of the difference as the frontier of an intersection.
  have h_eq : frontier (A \ B) = frontier (A ∩ Bᶜ) := by
    simp [Set.diff_eq]
  -- Transport the membership along the equality.
  have hx' : x ∈ frontier (A ∩ Bᶜ) := by
    simpa [h_eq] using hx
  -- Apply the existing inclusion for frontiers of intersections.
  have hx'' :
      x ∈ frontier A ∪ frontier (Bᶜ) :=
    (Topology.frontier_inter_subset_union_frontier
      (A := A) (B := Bᶜ)) hx'
  -- Replace `frontier (Bᶜ)` with `frontier B`.
  cases hx'' with
  | inl hA =>
      exact Or.inl hA
  | inr hBc =>
      have hB : x ∈ frontier B := by
        simpa [Topology.frontier_compl (A := B)] using hBc
      exact Or.inr hB

theorem Topology.nonempty_interior_closure_interior_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (interior A))).Nonempty ↔ (interior A).Nonempty := by
  -- First, translate the desired statement into a comparison of (in)equality
  -- with the empty set, using `Set.nonempty_iff_ne_empty`.
  have hNe :
      (interior (closure (interior A)) ≠ (∅ : Set X)) ↔
        interior A ≠ (∅ : Set X) := by
    -- Take the negation of the equivalence of emptiness already proved.
    have hEmpty :=
      Topology.interior_closure_interior_eq_empty_iff (A := A)
    exact (not_congr hEmpty)
  -- Rewrite `Nonempty` in terms of `≠ ∅` and conclude.
  simpa [Set.nonempty_iff_ne_empty] using hNe

theorem Topology.frontier_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior (closure (interior A)))) =
      frontier (closure (interior A)) := by
  -- Obtain the core set equality from idempotence of `closure ∘ interior`.
  have hEq :
      closure (interior (closure (interior A))) = closure (interior A) :=
    Topology.closure_interior_idempotent (A := A)
  -- Rewrite both frontiers using the established equality.
  simpa [frontier, hEq]

theorem Topology.closure_frontier_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP1 : Topology.P1 A) :
    closure (frontier A) ⊆ closure (interior A) := by
  -- First, use the existing lemma that the frontier of `A`
  -- is contained in `closure (interior A)` under `P1 A`.
  have h_subset : frontier A ⊆ closure (interior A) :=
    Topology.frontier_subset_closure_interior_of_P1 (A := A) hP1
  -- Taking closures preserves inclusions; simplify `closure (closure _)`.
  simpa [closure_closure] using closure_mono h_subset

theorem Topology.frontier_eq_univ_diff_interior_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    frontier A = (Set.univ : Set X) \ interior A := by
  -- Since `A` is dense, its closure is the whole space.
  have hClosure : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Rewrite `frontier A` using its definition and the closure equality.
  simpa [frontier, hClosure]

theorem Topology.closure_frontier_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (frontier A) = closure A ∩ closure (Aᶜ) := by
  -- First, `frontier A` is closed, hence its closure is itself.
  have h₁ : closure (frontier A) = frontier A :=
    Topology.closure_frontier_eq_frontier (A := A)
  -- Next, express `frontier A` as the intersection of the two closures.
  have h₂ : frontier A = closure A ∩ closure (Aᶜ) :=
    Topology.frontier_eq_closure_inter_closure_compl (A := A)
  -- Combine the two equalities.
  simpa [h₂] using h₁

theorem Topology.frontier_eq_closure_of_interior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = (∅ : Set X)) :
    frontier A = closure A := by
  simpa [frontier, hInt, Set.diff_empty]

theorem Topology.closure_interior_subset_closure_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  have h_subset : interior B ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
  exact closure_mono h_subset

theorem Topology.frontier_eq_closure_diff_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier A = closure A \ interior A := by
  rfl

theorem Topology.dense_iff_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ interior (Aᶜ) = (∅ : Set X) := by
  classical
  constructor
  · intro hDense
    exact interior_compl_eq_empty_of_dense (A := A) hDense
  · intro hIntEmpty
    -- Show `closure A = univ`, then invoke an existing equivalence.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      by_cases hx : x ∈ closure A
      · exact hx
      ·
        -- `x` belongs to the open set `(closure A)ᶜ`
        have hx_mem : x ∈ (closure A)ᶜ := by
          simpa [Set.mem_compl] using hx
        have hOpen : IsOpen ((closure A)ᶜ) :=
          isClosed_closure.isOpen_compl
        -- `(closure A)ᶜ` is an open subset of `Aᶜ`
        have h_subset : (closure A)ᶜ ⊆ Aᶜ := by
          intro y hy
          by_cases hAy : y ∈ A
          · have : y ∈ closure A := subset_closure hAy
            exact False.elim (hy this)
          · simpa [Set.mem_compl] using hAy
        -- Therefore it is contained in `interior (Aᶜ)`
        have hx_int : x ∈ interior (Aᶜ) :=
          (interior_maximal h_subset hOpen) hx_mem
        -- Contradicts the assumption `interior (Aᶜ) = ∅`
        simpa [hIntEmpty] using hx_int
    have h_closure_eq :
        closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact h_univ_subset
    exact
      ((Topology.dense_iff_closure_eq_univ (A := A)).2 h_closure_eq)

theorem Topology.dense_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hDenseA : Dense A) : Dense B := by
  -- The closure of a dense set is the whole space.
  have hClosureA : closure A = (Set.univ : Set X) := hDenseA.closure_eq
  -- Monotonicity of `closure` under the inclusion `A ⊆ B`.
  have hSubset : closure A ⊆ closure B := closure_mono hAB
  -- Hence `closure B` contains `univ`.
  have hUnivSubset : (Set.univ : Set X) ⊆ closure B := by
    simpa [hClosureA] using hSubset
  -- Now we have the desired equality `closure B = univ`.
  have hClosureB : closure B = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _x _hx; simp
    · exact hUnivSubset
  -- Translate the closure equality into the `Dense` property.
  simpa using (Topology.dense_iff_closure_eq_univ (A := B)).2 hClosureB

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P3 A := by
  -- `IsOpen (closure A)` is equivalent to `P3 (closure A)`.
  have hP3_closure : Topology.P3 (closure A) :=
    (Topology.P3_closure_iff_isOpen_closure (A := A)).mpr hOpen
  -- Transfer the `P3` property from `closure A` to `A`.
  exact Topology.P3_of_P3_closure (A := A) hP3_closure

theorem Topology.closure_interior_diff_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} : closure (interior A) \ A ⊆ frontier A := by
  intro x hx
  rcases hx with ⟨hxClInt, hxNotA⟩
  -- `x` lies in `closure A` because `closure (interior A) ⊆ closure A`.
  have hxClA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hxClInt
  -- `x` is not in `interior A` since it is not in `A`.
  have hxNotInt : x ∉ interior A := by
    intro hInt
    have : x ∈ A := interior_subset hInt
    exact hxNotA this
  -- Assemble the frontier membership.
  exact And.intro hxClA hxNotInt

theorem Topology.frontier_compl_eq_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (Aᶜ) = frontier A := by
  simpa using frontier_compl (A := A)

theorem Topology.innerInterior_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure A) := by
  intro x hx
  exact (interior_mono (subset_closure : A ⊆ closure A)) hx

theorem Topology.frontier_eq_empty_iff_isClosed_and_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier A = (∅ : Set X) ↔ (IsClosed A ∧ IsOpen A) := by
  constructor
  · intro hEmpty
    -- From `frontier A = ∅` we have `closure A ⊆ interior A`
    have hSub : closure A ⊆ interior A := by
      intro x hxCl
      by_contra hxInt
      have : x ∈ closure A \ interior A := ⟨hxCl, hxInt⟩
      have : x ∈ (∅ : Set X) := by
        simpa [hEmpty] using this
      exact this.elim
    -- Show `closure A = A`
    have hClosEq : closure A = A := by
      apply Set.Subset.antisymm
      · intro x hx
        have : x ∈ interior A := hSub hx
        exact interior_subset this
      · exact subset_closure
    -- Show `interior A = A`
    have hIntEq : interior A = A := by
      apply Set.Subset.antisymm
      · intro x hx; exact interior_subset hx
      · intro x hx
        have : x ∈ closure A := subset_closure hx
        have : x ∈ interior A := hSub this
        exact this
    -- Conclude that `A` is both closed and open
    have hClosed : IsClosed A := by
      simpa [hClosEq] using (isClosed_closure : IsClosed (closure A))
    have hOpen : IsOpen A := by
      simpa [hIntEq] using (isOpen_interior : IsOpen (interior A))
    exact ⟨hClosed, hOpen⟩
  · rintro ⟨hClosed, hOpen⟩
    -- If `A` is clopen, its frontier is empty
    have hClos : closure A = A := hClosed.closure_eq
    have hInt  : interior A = A := hOpen.interior_eq
    simpa [frontier, hClos, hInt, Set.diff_self]

theorem Topology.interior_subset_closure_of_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ closure B) :
    interior A ⊆ closure B := by
  intro x hxIntA
  exact hAB (interior_subset hxIntA)

theorem Topology.frontier_closure_interior_subset_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (closure (interior A)) ⊆ frontier A := by
  intro x hx
  -- `hx.1` gives `x ∈ closure (closure (interior A))`; simplify the double closure.
  have hClCI : x ∈ closure (interior A) := by
    simpa [closure_closure] using hx.1
  -- Monotonicity of `closure` under `interior A ⊆ A`.
  have hClA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (A := A)) hClCI
  -- Show that `x ∉ interior A`; otherwise we contradict `hx.2`.
  have hNotIntA : x ∉ interior A := by
    intro hIntA
    have hSubset :
        interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (A := A)
    have : x ∈ interior (closure (interior A)) := hSubset hIntA
    exact hx.2 this
  exact And.intro hClA hNotIntA

theorem Topology.P1_closure_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) : Topology.P1 (closure (closure A)) := by
  -- First, obtain `P1` for `closure A` from the existing lemma.
  have hP1_closure : Topology.P1 (closure A) :=
    Topology.P1_closure_of_P1 (A := A) hP1
  -- Rewrite `closure (closure A)` as `closure A` and conclude.
  simpa [closure_closure] using hP1_closure

theorem Topology.frontier_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    frontier A ⊆ Aᶜ := by
  intro x hx
  -- From `hx : x ∈ frontier A`, we have `x ∉ interior A`.
  have h_not_int : x ∉ interior A := hx.2
  -- Since `A` is open, `interior A = A`.
  have hIntEq : interior A = A := hA.interior_eq
  -- Therefore `x ∉ A`.
  have h_notA : x ∉ A := by
    simpa [hIntEq] using h_not_int
  -- Hence `x` belongs to the complement of `A`.
  simpa [Set.mem_compl] using h_notA