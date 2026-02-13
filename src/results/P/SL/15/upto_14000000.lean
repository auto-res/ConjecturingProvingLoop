

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hP2.trans h_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  open Set in
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_mono : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    exact interior_mono h_closure_mono
  exact hP2.trans h_subset

theorem isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have hInt : x ∈ interior A := by
    simpa [IsOpen.interior_eq hA] using hx
  exact subset_closure hInt

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hx
  -- `closure A` is a neighborhood of `x`
  have h_nhds_closure : closure A ∈ 𝓝 x := by
    have h_nhdsA : A ∈ 𝓝 x := hA.mem_nhds hx
    exact Filter.mem_of_superset h_nhdsA subset_closure
  -- hence `x` belongs to the interior of `closure A`
  have h_mem_closure : x ∈ interior (closure A) :=
    (mem_interior_iff_mem_nhds).2 h_nhds_closure
  -- rewrite to obtain the desired membership
  simpa [hA.interior_eq] using h_mem_closure

theorem isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  exact (P2_implies_P3 (X := X) (A := A)) (isOpen_implies_P2 (X := X) (A := A) hA)

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior (closure (interior A)) ⊆ closure A := by
  open Set in
  have h₁ : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h₂ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h₁
  exact h₂.trans interior_subset

theorem dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have h_closure : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure, interior_univ]

theorem interior_closure_interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior (closure (interior A)) ⊆ interior (closure A) := by
  open Set in
  have h_mono : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  exact interior_mono h_mono

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact ⟨Topology.P2_implies_P1 (X := X) (A := A) hP2,
         Topology.P2_implies_P3 (X := X) (A := A) hP2⟩

theorem interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have hIntEq : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  have h_closure : x ∈ closure (interior A) := subset_closure hx
  simpa [hIntEq] using h_closure

theorem interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  intro x hx
  have h_mono : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure)
  have h_eq : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  have hx' : x ∈ interior (interior A) := by
    simpa [h_eq] using hx
  exact h_mono hx'

theorem interior_has_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  exact Topology.interior_subset_interior_closure_interior (X := X) (A := A)

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    -- `closure (interior A)` is contained in `closure A`
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- `closure A` is contained in `closure (interior A)`
    have h₂ : closure A ⊆ closure (interior A) := by
      have h_sub : A ⊆ closure (interior A) := hP1
      have : closure A ⊆ closure (closure (interior A)) := closure_mono h_sub
      simpa using this
    exact Set.Subset.antisymm h₂ h₁
  · intro hEq
    dsimp [Topology.P1]
    intro x hx
    have hx_closure : x ∈ closure A := subset_closure hx
    simpa [hEq] using hx_closure

theorem interior_closure_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P1 (X := X) (A := interior (closure A)) h_open

theorem interior_closure_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior (closure A)) h_open

theorem interior_closure_has_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure A)) h_open

theorem interior_has_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := A) hx
  have hIntInt : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  simpa [hIntInt] using hx'

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl h₁ =>
      have hxA : x ∈ interior (closure A) := hA h₁
      have h_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have : closure A ⊆ closure (A ∪ B) := closure_mono (Set.subset_union_left)
        exact interior_mono this
      exact h_mono hxA
  | inr h₂ =>
      have hxB : x ∈ interior (closure B) := hB h₂
      have h_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have : closure B ⊆ closure (A ∪ B) := closure_mono (Set.subset_union_right)
        exact interior_mono this
      exact h_mono hxB

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hAx : x ∈ closure (interior A) := hA hA_mem
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hIntSubset : interior A ⊆ interior (A ∪ B) := by
          have h_sub : A ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono h_sub
        exact closure_mono hIntSubset
      exact h_subset hAx
  | inr hB_mem =>
      have hBx : x ∈ closure (interior B) := hB hB_mem
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hIntSubset : interior B ⊆ interior (A ∪ B) := by
          have h_sub : B ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono h_sub
        exact closure_mono hIntSubset
      exact h_subset hBx

theorem P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    have h_closure : closure A = A := hA_closed.closure_eq
    have h_subset : A ⊆ interior A := by
      simpa [Topology.P3, h_closure] using hP3
    have h_eq : interior A = A := Set.Subset.antisymm interior_subset h_subset
    have h_open_int : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using h_open_int
  · intro hA_open
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hA_open

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hA_mem =>
      have hxA : x ∈ interior (closure (interior A)) := hA hA_mem
      have h_mono : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSubset : interior A ⊆ interior (A ∪ B) := by
          have : A ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        have hClosMono : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSubset
        exact interior_mono hClosMono
      exact h_mono hxA
  | inr hB_mem =>
      have hxB : x ∈ interior (closure (interior B)) := hB hB_mem
      have h_mono : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have hIntSubset : interior B ⊆ interior (A ∪ B) := by
          have : B ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        have hClosMono : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono hIntSubset
        exact interior_mono hClosMono
      exact h_mono hxB

theorem P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen (X := X) (A := closure A) h_closed)

theorem P2_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    exact
      (Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).mp hP3
  · intro hA_open
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hA_open

theorem P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  have h_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  have hx' : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  have h_mono : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int_subset : interior A ⊆ interior (closure A) := by
      have h_subset : A ⊆ closure A := subset_closure
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact h_mono hx'

theorem P1_closed_iff_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P1 A ↔ A = closure (interior A) := by
  have h_closure_eq : closure A = A := hA_closed.closure_eq
  have h₀ : Topology.P1 A ↔ closure A = closure (interior A) :=
    Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  simpa [h_closure_eq] using h₀

theorem empty_has_all_P {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  have hP1 : Topology.P1 (∅ : Set X) := by
    dsimp [Topology.P1]
    exact Set.empty_subset _
  have hP2 : Topology.P2 (∅ : Set X) := by
    dsimp [Topology.P2]
    exact Set.empty_subset _
  have hP3 : Topology.P3 (∅ : Set X) := by
    dsimp [Topology.P3]
    exact Set.empty_subset _
  exact ⟨hP1, hP2, hP3⟩

theorem isOpen_has_all_P {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.isOpen_implies_P1 (X := X) (A := A) hA,
     Topology.isOpen_implies_P2 (X := X) (A := A) hA,
     Topology.isOpen_implies_P3 (X := X) (A := A) hA⟩

theorem P2_closed_iff_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  exact
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed).trans
      ((Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).symm)

theorem P1_implies_interior_closure_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  simpa [h_closure_eq]

theorem P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_P3_closed (X := X) (A := closure A) h_closed)

theorem closure_interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  have h_subset : interior A ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := A)
  have h_mono : closure (interior A) ⊆
      closure (interior (closure (interior A))) :=
    closure_mono h_subset
  exact h_mono hx

theorem P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P1]
  intro x hx
  exact (closure_mono hP3) hx

theorem P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact Topology.P1_implies_P1_closure (X := X) (A := A) hP1

theorem univ_has_all_P {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧
      Topology.P2 (Set.univ : Set X) ∧
        Topology.P3 (Set.univ : Set X) := by
  simpa using
    (Topology.isOpen_has_all_P (X := X) (A := (Set.univ : Set X)) isOpen_univ)

theorem interior_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  intro x hx
  exact (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx

theorem P2_closure_interior_iff_isOpen_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P2_closed_iff_isOpen (X := X) (A := closure (interior A)) h_closed)

theorem interior_closure_interior_has_all_P {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) ∧
      Topology.P2 (interior (closure (interior A))) ∧
        Topology.P3 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact
    Topology.isOpen_has_all_P
      (X := X)
      (A := interior (closure (interior A)))
      h_open

theorem P2_implies_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1

theorem P3_closure_interior_iff_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen (X := X) (A := closure (interior A)) h_closed)

theorem interior_closure_nonempty_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP3 hA
  rcases hA with ⟨x, hx⟩
  exact ⟨x, hP3 hx⟩

theorem isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP1A : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA
  exact Topology.P1_implies_P1_closure (X := X) (A := A) hP1A

theorem P2_implies_interior_closure_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have h_closure_eq : closure A = closure (interior A) :=
    Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hP2
  simpa [h_closure_eq]

theorem P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3Closure
  dsimp [Topology.P3] at hP3Closure ⊢
  intro x hx
  have hx_closure : x ∈ closure A := subset_closure hx
  have hx_int : x ∈ interior (closure (closure A)) := hP3Closure hx_closure
  simpa [closure_closure] using hx_int

theorem P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P3 A) :
    Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3]
  intro x hx
  obtain ⟨A, hA_mem, hxA⟩ := Set.mem_sUnion.1 hx
  have hP3A := h𝒜 A hA_mem
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have h_mono : interior (closure A) ⊆ interior (closure (⋃₀ 𝒜)) := by
    have h_subset : closure A ⊆ closure (⋃₀ 𝒜) := by
      have : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
      exact closure_mono this
    exact interior_mono h_subset
  exact h_mono hx_int

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P1 A) :
    Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP1A := h𝒜 A hA_mem
  have hx_closure : x ∈ closure (interior A) := hP1A hxA
  have h_mono : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) := by
    have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
      have h_subset : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact h_mono hx_closure

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ A, A ∈ 𝒜 → Topology.P2 A) :
    Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := h𝒜 A hA_mem
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_mono : interior (closure (interior A)) ⊆
      interior (closure (interior (⋃₀ 𝒜))) := by
    have h_int_subset : interior A ⊆ interior (⋃₀ 𝒜) := by
      have h_subset : A ⊆ ⋃₀ 𝒜 := Set.subset_sUnion_of_mem hA_mem
      exact interior_mono h_subset
    have h_closure_subset : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact h_mono hx_int

theorem P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2
  · intro hP3
    dsimp [Topology.P2]
    intro x hx
    have hx' : x ∈ interior (closure A) := by
      dsimp [Topology.P3] at hP3
      exact hP3 hx
    simpa [hA.interior_eq] using hx'

theorem interior_closure_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP2 hA
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact
    Topology.interior_closure_nonempty_of_P3 (X := X) (A := A) hP3 hA

theorem P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _h
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hA
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2

theorem dense_union_has_P3 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense A → Topology.P3 (A ∪ B) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have h_closureA : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have h_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
    have : closure A ⊆ closure (A ∪ B) := by
      have h_sub : A ⊆ A ∪ B := Set.subset_union_left
      exact closure_mono h_sub
    simpa [h_closureA] using this
  have h_closure_union : closure (A ∪ B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; exact Set.mem_univ y
    · exact h_subset
  simpa [h_closure_union, interior_univ] using Set.mem_univ x

theorem interior_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h₁ :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h₁
  ·
    have h₂ :
        interior (closure A) ⊆
          interior (closure (interior (closure A))) :=
      interior_subset_interior_closure_interior
        (X := X) (A := closure A)
    simpa using h₂

theorem P3_closed_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hP3A hP3B
  -- From the closedness and `P3` property we deduce that `A` and `B` are open
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_isOpen (X := X) (A := B) hB_closed).1 hP3B
  -- The intersection of open (resp. closed) sets is open (resp. closed)
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  have hClosedInter : IsClosed (A ∩ B) := hA_closed.inter hB_closed
  -- Apply the closed–open equivalence for `P3` to the intersection
  exact
    (Topology.P3_closed_iff_isOpen (X := X) (A := A ∩ B) hClosedInter).2
      hOpenInter

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA).trans
      (Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA)

theorem P3_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    have h_subset : A ⊆ interior A := by
      dsimp [Topology.P3] at hP3
      simpa [hA_closed.closure_eq] using hP3
    exact Set.Subset.antisymm interior_subset h_subset
  · intro hIntEq
    have hOpen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [hIntEq] using this
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem P3_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X] {f : ι → Set X}
    (h : ∀ i, Topology.P3 (f i)) : Topology.P3 (⋃ i, f i) := by
  dsimp [Topology.P3] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (f i)) := (h i) hxi
  have h_mono : interior (closure (f i)) ⊆ interior (closure (⋃ i, f i)) := by
    have h_subset : closure (f i) ⊆ closure (⋃ j, f j) := by
      have h_sub : f i ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_subset
  exact h_mono hx_int

theorem P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h₁ := (Topology.P2_closure_iff_P3_closure (X := X) (A := A))
  have h₂ := (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A))
  exact h₁.trans h₂

theorem P1_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X] {f : ι → Set X}
    (h : ∀ i, Topology.P1 (f i)) : Topology.P1 (⋃ i, f i) := by
  dsimp [Topology.P1] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_closure : x ∈ closure (interior (f i)) := (h i) hxi
  have h_mono : closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
    have h_int_subset : interior (f i) ⊆ interior (⋃ j, f j) := by
      have h_subset : f i ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact h_mono hx_closure

theorem P2_closed_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hP2A hP2B
  -- Using the closedness of `A` and `B`, translate the `P2` property into openness.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := B) hB_closed).1 hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- The intersection of two closed sets is closed.
  have hClosedInter : IsClosed (A ∩ B) := hA_closed.inter hB_closed
  -- Convert the openness of the intersection back to the `P2` property.
  exact
    (Topology.P2_closed_iff_isOpen (X := X) (A := A ∩ B) hClosedInter).2 hOpenInter

theorem P2_iUnion {ι : Sort _} {X : Type _} [TopologicalSpace X] {f : ι → Set X}
    (h : ∀ i, Topology.P2 (f i)) : Topology.P2 (⋃ i, f i) := by
  dsimp [Topology.P2] at h ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (interior (f i))) := (h i) hxi
  have h_mono :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ j, f j))) := by
    have h_int_subset :
        interior (f i) ⊆ interior (⋃ j, f j) := by
      have h_subset : f i ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    have h_closure_subset :
        closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) :=
      closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact h_mono hx_int

theorem closure_interior_closure_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  have h_subset :
      interior (closure A) ⊆ interior (closure (interior (closure A))) :=
    Topology.interior_subset_interior_closure_interior (X := X) (A := closure A)
  have h_mono :
      closure (interior (closure A)) ⊆
        closure (interior (closure (interior (closure A)))) :=
    closure_mono h_subset
  exact h_mono hx

theorem interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_interior_closure_eq (X := X) (A := interior A))

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2Closure
  have hP3Closure : Topology.P3 (closure A) :=
    ((Topology.P2_closure_iff_P3_closure (X := X) (A := A)).1 hP2Closure)
  exact Topology.P3_closure_implies_P3 (X := X) (A := A) hP3Closure

theorem isOpen_inter_has_all_P {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.isOpen_has_all_P (X := X) (A := A ∩ B) hOpen

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First, translate `P2` into openness for a closed set.
  have h₁ : Topology.P2 A ↔ IsOpen A :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed)
  -- Relate openness to the equality `interior A = A`.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hIntEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hIntEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x _
  simpa [interior_univ, closure_univ] using (Set.mem_univ x)

theorem dense_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure A) := by
  intro hDense
  have h_closure_eq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure_eq] using (Topology.P1_univ (X := X))

theorem P2_imp_eq_empty_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  have hInnerEmpty : interior (closure (interior A)) = (∅ : Set X) := by
    simpa [hIntEmpty, closure_empty, interior_empty]
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ interior (closure (interior A)) := hP2 hx
    simpa [hInnerEmpty] using this
  · exact Set.empty_subset _

theorem P3_interior_closure_eq_empty_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) :
    interior (closure A) = (∅ : Set X) ↔ A = (∅ : Set X) := by
  classical
  constructor
  · intro hInt
    by_cases hA : (A = (∅ : Set X))
    · exact hA
    · exfalso
      -- From `A ≠ ∅` we obtain a witness `x ∈ A`.
      have hNonempty : A.Nonempty := by
        by_contra hNone
        have hEq : A = (∅ : Set X) := (Set.not_nonempty_iff_eq_empty).1 hNone
        exact hA hEq
      rcases hNonempty with ⟨x, hx⟩
      -- Thanks to `P3`, this point lies in `interior (closure A)`.
      have hxInt : x ∈ interior (closure A) := hP3 hx
      -- But `interior (closure A)` is empty, contradiction.
      have : x ∈ (∅ : Set X) := by
        simpa [hInt] using hxInt
      exact this.elim
  · intro hA
    simpa [hA, closure_empty, interior_empty]

theorem dense_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _
  have hEq : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hEq, interior_univ, closure_univ] using this

theorem interior_closure_interior_eq_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]

theorem P3_closed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP3
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem P2_iff_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔ (Topology.P3 A ∧ closure A = closure (interior A)) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    have hEq : closure A = closure (interior A) :=
      Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hP2
    exact ⟨hP3, hEq⟩
  · rintro ⟨hP3, hEq⟩
    dsimp [Topology.P2]
    intro x hx
    have hxInt : x ∈ interior (closure A) := hP3 hx
    simpa [hEq] using hxInt

theorem dense_closure_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense A) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  have h : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h, interior_univ, closure_univ]

theorem P3_iff_closure_mem_nhds {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∀ x ∈ A, closure A ∈ 𝓝 x := by
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    intro x hx
    have hx_int : x ∈ interior (closure A) := hP3 hx
    exact (mem_interior_iff_mem_nhds).1 hx_int
  · intro h
    dsimp [Topology.P3]
    intro x hx
    have h_nhds : closure A ∈ 𝓝 x := h x hx
    exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem dense_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure A) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  have h_closure_eq : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [closure_closure, h_closure_eq, interior_univ] using this

theorem P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x _
  simpa [closure_univ, interior_univ] using (Set.mem_univ x)

theorem closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  have h := interior_closure_interior_closure_eq (X := X) (A := A)
  simpa [h]

theorem interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : interior (closure A) = (Set.univ : Set X) := by
  have h_closure : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure, interior_univ]

theorem P1_imp_eq_empty_of_empty_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hIntEmpty : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ closure (interior A) := hP1 hx
    simpa [hIntEmpty, closure_empty] using this
  · exact Set.empty_subset _

theorem P3_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hP3 : Topology.P3 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- From `P3`, the point `x` belongs to `interior (closure A)`.
  have hx_intA : x ∈ interior (closure A) := hP3 hxA
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_closure_mono : closure A ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves inclusion.
  have h_int_mono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure_mono
  exact h_int_mono hx_intA

theorem interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
      simpa using
        (Topology.interior_closure_interior_closure_eq
          (X := X) (A := interior (closure A)))
    _ = interior (closure A) := by
      simpa using
        (Topology.interior_closure_interior_closure_eq
          (X := X) (A := A))

theorem P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  have h := (Topology.univ_has_all_P (X := X))
  exact h.2.1

theorem P2_subset_interior_closure_interior_of_subset {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hP2 : Topology.P2 A) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_mono : interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
    have h_int : interior A ⊆ interior B := interior_mono hAB
    have h_closure : closure (interior A) ⊆ closure (interior B) := closure_mono h_int
    exact interior_mono h_closure
  exact h_mono hx_int

theorem closure_interior_eq_univ_of_P1_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hDense : Dense A) :
    closure (interior A) = (Set.univ : Set X) := by
  -- From `P1`, we have `closure A = closure (interior A)`.
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Since `A` is dense, `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Combining the two equalities yields the desired result.
  simpa [h_closure_eq] using h_closure_univ

theorem closure_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    have h₁ : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (X := X) (A := A)
    have h₂ :
        closure (interior A) ⊆
          closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂

theorem P3_and_P1_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 A → Topology.P2 A := by
  intro hP3 hP1
  dsimp [Topology.P2]
  intro x hx
  have hx_int_clA : x ∈ interior (closure A) := hP3 hx
  have h_cl_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  simpa [h_cl_eq] using hx_int_clA

theorem interior_closure_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact subset_closure hx

theorem P1_subset_closure_interior_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1 : Topology.P1 A) :
    A ⊆ closure (interior B) := by
  intro x hxA
  have hx_cl_intA : x ∈ closure (interior A) := hP1 hxA
  have h_int_subset : interior A ⊆ interior B := interior_mono hAB
  have h_cl_subset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_subset
  exact h_cl_subset hx_cl_intA

theorem P2_iff_closureInterior_mem_nhds {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∀ x ∈ A, closure (interior A) ∈ 𝓝 x := by
  classical
  constructor
  · intro hP2 x hx
    have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
    exact (mem_interior_iff_mem_nhds).1 hx_int
  · intro h
    dsimp [Topology.P2]
    intro x hx
    have h_nhds : closure (interior A) ∈ 𝓝 x := h x hx
    exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1_and_P3 (X := X) (A := A) hP2
  · rintro ⟨hP1, hP3⟩
    exact Topology.P3_and_P1_implies_P2 (X := X) (A := A) hP3 hP1

theorem closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  have h1 :=
    interior_closure_interior_closure_interior_eq (X := X) (A := A)
  have h2 :=
    closure_interior_closure_eq (X := X) (A := A)
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
      simpa [h1]
    _ = closure (interior A) := by
      simpa using h2

theorem interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  calc
    interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
      simpa using
        (Topology.interior_closure_interior_closure_eq
          (X := X) (A := interior (closure (interior A))))
    _ = interior (closure (interior A)) := by
      simpa using
        (Topology.interior_closure_interior_closure_interior_eq
          (X := X) (A := A))

theorem P1_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (closure A)) ↔ Topology.P1 (closure A) := by
  simpa [closure_closure]

theorem closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem dense_points_mem_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → ∀ x : X, x ∈ closure A := by
  intro hDense x
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Trivially, every point belongs to `univ`.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    trivial
  -- Rewriting with `h_closure` gives the desired membership.
  simpa [h_closure] using hx_univ

theorem P3_implies_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior (closure A))`
    have h_sub : A ⊆ interior (closure A) := hP3
    have : closure A ⊆ closure (interior (closure A)) := closure_mono h_sub
    exact this
  · -- `closure (interior (closure A)) ⊆ closure A`
    have h_sub : interior (closure A) ⊆ closure A := interior_subset
    have : closure (interior (closure A)) ⊆ closure A := by
      simpa [closure_closure] using closure_mono h_sub
    exact this

theorem P2_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  simpa [Topology.P2, closure_closure]

theorem interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, move from `interior (closure (interior A))` to `interior (closure A)`.
  have hx' : x ∈ interior (closure A) :=
    interior_closure_interior_subset_interior_closure (X := X) (A := A) hx
  -- Any point of `interior (closure A)` belongs to the closure of `interior (closure A)`.
  have h_subset : interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  exact h_subset hx'

theorem closure_interior_closure_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure A))) = closure (interior (closure A)) := by
  simpa [closure_closure]

theorem P3_closure_and_P1_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P1 A → Topology.P2 A := by
  intro hP3Closure hP1
  have hP3A : Topology.P3 A :=
    Topology.P3_closure_implies_P3 (X := X) (A := A) hP3Closure
  exact
    Topology.P3_and_P1_implies_P2 (X := X) (A := A) hP3A hP1

theorem closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, collapse three inner `closure ∘ interior` pairs.
  have h₁ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior A) :=
    closure_interior_closure_interior_closure_interior_eq (X := X) (A := A)
  -- Apply `closure ∘ interior` once more to both sides of `h₁`.
  have h₂ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using congrArg (fun S : Set X => closure (interior S)) h₁
  -- Finally, collapse the remaining pair.
  have h₃ : closure (interior (closure (interior A))) = closure (interior A) :=
    closure_interior_closure_eq (X := X) (A := A)
  simpa [h₃] using h₂

theorem denseInterior_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P1 A := by
  dsimp [Topology.P1]
  intro x hx
  have h_closure : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_closure] using this

theorem closure_interior_inter_eq_closure_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) = closure (interior A ∩ interior B) := by
  simpa [interior_inter]

theorem interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hx
  have hxA : x ∈ A := interior_subset hx
  exact subset_closure hxA

theorem P3_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P3 (closure A) := by
  simpa [closure_closure]

theorem denseInterior_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- `closure (interior A)` is the whole space
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- hence its interior is also the whole space
  have h_int_eq : interior (closure (interior A)) = (Set.univ : Set X) := by
    have : interior (closure (interior A)) = interior ((Set.univ : Set X)) := by
      simpa [h_closure_int] using rfl
    simpa [interior_univ] using this
  -- `interior (closure (interior A)) ⊆ interior (closure A)`
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_mono : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono h_closure_mono
  -- Therefore, `interior (closure A)` is the whole space
  have h_univ_subset : (Set.univ : Set X) ⊆ interior (closure A) := by
    simpa [h_int_eq] using h_subset
  -- Conclude the desired membership
  have hx_in : x ∈ interior (closure A) := h_univ_subset (by trivial)
  exact hx_in

theorem P3_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A ⊆ interior (closure A) := by
  intro hP3
  intro x hx
  exact hP3 hx

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : interior (closure A) ⊆ interior (closure B) := by
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  exact interior_mono h_closure

theorem denseInterior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 A := by
  intro hDense
  have hP1 : Topology.P1 A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  have hP3 : Topology.P3 A :=
    Topology.denseInterior_implies_P3 (X := X) (A := A) hDense
  exact (Topology.P3_and_P1_implies_P2 (X := X) (A := A)) hP3 hP1

theorem P3_implies_P2_iff_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (Topology.P2 A ↔ closure A = closure (interior A)) := by
  intro hP3
  have h₁ :=
    (Topology.P2_iff_P3_and_closure_eq_closure_interior (X := X) (A := A))
  have h₂ :
      (Topology.P3 A ∧ closure A = closure (interior A)) ↔
        closure A = closure (interior A) := by
    constructor
    · intro h
      exact h.2
    · intro hEq
      exact And.intro hP3 hEq
  exact h₁.trans h₂

theorem P2_subset_interior_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP2 : Topology.P2 A) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- From `P2`, the point `x` lies in `interior (closure (interior A))`.
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Since `A ⊆ B`, the interior of `A` is included in `B`.
  have h_int_subset : interior A ⊆ B := by
    intro y hyInt
    have : y ∈ A := interior_subset hyInt
    exact hAB this
  -- Taking closures preserves inclusion.
  have h_closure_subset : closure (interior A) ⊆ closure B :=
    closure_mono h_int_subset
  -- Taking interiors preserves inclusion as well.
  have h_int_mono : interior (closure (interior A)) ⊆ interior (closure B) :=
    interior_mono h_closure_subset
  -- Conclude the desired membership.
  exact h_int_mono hx_int

theorem closure_interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- First, note that `interior A` is contained in `interior (closure A)`.
  have h_int : interior A ⊆ interior (closure A) := by
    have h_subset : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono h_subset
  -- Taking closures preserves inclusions.
  exact closure_mono h_int

theorem P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    -- From `A ⊆ closure (interior A)` we deduce the desired inclusion of closures.
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h
  · intro hSubset
    -- Use `closure` monotonicity together with `A ⊆ closure A`.
    dsimp [Topology.P1]
    intro x hx
    have hx_cl : x ∈ closure A := subset_closure hx
    exact hSubset hx_cl

theorem interior_closure_eq_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA_closed.closure_eq]

theorem closureInterior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (closure (interior A)).Nonempty := by
  intro hP1 hA
  rcases hA with ⟨x, hx⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  exact ⟨x, hx_cl⟩

theorem P1_and_dense_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Topology.P2 A := by
  intro hP1 hDense
  dsimp [Topology.P2]
  intro x hx
  -- From `P1` and density we know `closure (interior A)` is the whole space.
  have h_closure_univ :
      closure (interior A) = (Set.univ : Set X) :=
    Topology.closure_interior_eq_univ_of_P1_and_dense
      (X := X) (A := A) hP1 hDense
  -- Hence its interior is also the whole space.
  have h_int_univ :
      interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure_univ, interior_univ]
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int_univ] using this

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ×ˢ B) := by
  intro hA hB
  dsimp [Topology.P3] at hA hB ⊢
  intro p hp
  -- Coordinates of the point `p`.
  have hAx : p.1 ∈ A := hp.1
  have hBy : p.2 ∈ B := hp.2
  -- Apply the `P3` property to each coordinate.
  have hIntA : p.1 ∈ interior (closure A) := hA hAx
  have hIntB : p.2 ∈ interior (closure B) := hB hBy
  -- The product of these interiors is an open neighbourhood of `p`.
  have hOpen :
      IsOpen (Set.prod (interior (closure A)) (interior (closure B))) :=
    (isOpen_interior).prod isOpen_interior
  have hMem :
      (p : X × Y) ∈ Set.prod (interior (closure A)) (interior (closure B)) :=
    ⟨hIntA, hIntB⟩
  -- This neighbourhood is contained in `closure (A ×ˢ B)`.
  have hSub :
      Set.prod (interior (closure A)) (interior (closure B)) ⊆
        closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    have hqA_cl : q.1 ∈ closure A := interior_subset hqA
    have hqB_cl : q.2 ∈ closure B := interior_subset hqB
    have h_eq :
        closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
      simpa using closure_prod_eq
    have : (q : X × Y) ∈ (closure A) ×ˢ (closure B) :=
      ⟨hqA_cl, hqB_cl⟩
    simpa [h_eq] using this
  -- Turn the neighbourhood into an interior membership.
  have h_nhds :
      closure (A ×ˢ B) ∈ 𝓝 p :=
    Filter.mem_of_superset (hOpen.mem_nhds hMem) hSub
  exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ×ˢ B) := by
  intro hA hB
  dsimp [Topology.P1] at hA hB ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply the `P1` property coordinate-wise.
  have hA' : p.1 ∈ closure (interior A) := hA hpA
  have hB' : p.2 ∈ closure (interior B) := hB hpB
  -- Identify the target closure set using `interior_prod_eq` and `closure_prod_eq`.
  have h_closure_prod :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa [interior_prod_eq] using
      (closure_prod_eq (s := interior A) (t := interior B))
  -- Conclude the desired membership.
  have : (p : X × Y) ∈ closure (interior A) ×ˢ closure (interior B) :=
    ⟨hA', hB'⟩
  simpa [h_closure_prod] using this

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ×ˢ B) := by
  intro hA hB
  dsimp [Topology.P2] at hA hB ⊢
  intro p hp
  -- Apply the `P2` property to both coordinates of `p`.
  have hpA : p.1 ∈ interior (closure (interior A)) := hA hp.1
  have hpB : p.2 ∈ interior (closure (interior B)) := hB hp.2
  -- The product of these interiors is an open neighbourhood of `p`.
  have hOpen :
      IsOpen (Set.prod (interior (closure (interior A)))
                       (interior (closure (interior B)))) := by
    have h1 : IsOpen (interior (closure (interior A))) := isOpen_interior
    have h2 : IsOpen (interior (closure (interior B))) := isOpen_interior
    exact h1.prod h2
  have hMem :
      (p : X × Y) ∈
        Set.prod (interior (closure (interior A)))
                 (interior (closure (interior B))) := by
    exact ⟨hpA, hpB⟩
  -- Show that this neighbourhood is contained in `closure (interior (A ×ˢ B))`.
  have hSubset :
      Set.prod (interior (closure (interior A)))
               (interior (closure (interior B))) ⊆
        closure (interior (A ×ˢ B)) := by
    intro q hq
    rcases hq with ⟨hqA, hqB⟩
    -- Each coordinate lies in the corresponding closure.
    have hqA_cl : q.1 ∈ closure (interior A) := interior_subset hqA
    have hqB_cl : q.2 ∈ closure (interior B) := interior_subset hqB
    have hProdMem :
        (q : X × Y) ∈ closure (interior A) ×ˢ closure (interior B) :=
      ⟨hqA_cl, hqB_cl⟩
    -- Relate product closures to the closure of a product.
    have h_closure_prod :
        closure ((interior A) ×ˢ (interior B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      simpa using closure_prod_eq (s := interior A) (t := interior B)
    have hq_mem_closure_prod :
        (q : X × Y) ∈ closure ((interior A) ×ˢ (interior B)) := by
      simpa [h_closure_prod] using hProdMem
    -- Identify `interior (A ×ˢ B)`.
    have h_int_prod :
        interior (A ×ˢ B) = (interior A) ×ˢ (interior B) := by
      simpa using interior_prod_eq (s := A) (t := B)
    simpa [h_int_prod] using hq_mem_closure_prod
  -- Turn the neighbourhood inclusion into an interior membership.
  have hNhds :
      closure (interior (A ×ˢ B)) ∈ 𝓝 p :=
    Filter.mem_of_superset (hOpen.mem_nhds hMem) hSubset
  exact (mem_interior_iff_mem_nhds).2 hNhds

theorem P3_implies_P2_iff_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (Topology.P2 A ↔ Topology.P1 A) := by
  intro hP3
  -- Start from the general equivalence already available in the library.
  have h₁ : Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) :=
    (Topology.P2_iff_P1_and_P3 (X := X) (A := A))
  -- Under the assumption `P3 A`, the conjunction simplifies.
  have h₂ : (Topology.P1 A ∧ Topology.P3 A) ↔ Topology.P1 A := by
    constructor
    · intro h; exact h.1
    · intro hP1; exact And.intro hP1 hP3
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem P3_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Topology.P3 (A ×ˢ (Set.univ : Set Y)) → Topology.P3 A := by
  intro hProd
  dsimp [Topology.P3] at hProd
  dsimp [Topology.P3]
  intro x hxA
  classical
  -- Choose an arbitrary element of `Y` to build a point in the product.
  let y : Y := Classical.arbitrary Y
  have h_mem_prod : (x, y) ∈ A ×ˢ (Set.univ : Set Y) := by
    exact ⟨hxA, Set.mem_univ y⟩
  -- Apply the `P3` property of the product.
  have h_int_prod : (x, y) ∈ interior (closure (A ×ˢ (Set.univ : Set Y))) :=
    hProd h_mem_prod
  -- Identify the closure of the product with a product of closures.
  have h_closure_prod :
      closure (A ×ˢ (Set.univ : Set Y)) = (closure A) ×ˢ (Set.univ : Set Y) := by
    simpa using closure_prod_eq (s := A) (t := (Set.univ : Set Y))
  -- Rewrite the interior of this product.
  have h_int_prod_eq :
      interior ((closure A) ×ˢ (Set.univ : Set Y)) =
        interior (closure A) ×ˢ (Set.univ : Set Y) := by
    simpa using interior_prod_eq (s := closure A) (t := (Set.univ : Set Y))
  -- Transport membership through these equalities.
  have h_int_prod' : (x, y) ∈ interior ((closure A) ×ˢ (Set.univ : Set Y)) := by
    simpa [h_closure_prod] using h_int_prod
  have h_int_prod'' : (x, y) ∈ interior (closure A) ×ˢ (Set.univ : Set Y) := by
    simpa [h_int_prod_eq] using h_int_prod'
  -- Conclude the desired membership for `x`.
  exact (Set.mem_prod.1 h_int_prod'').1

theorem P1_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Topology.P1 (A ×ˢ (Set.univ : Set Y)) → Topology.P1 A := by
  intro hProd
  dsimp [Topology.P1] at hProd
  dsimp [Topology.P1]
  intro x hxA
  classical
  have y : Y := Classical.arbitrary Y
  have h_mem_prod : (x, y) ∈ A ×ˢ (Set.univ : Set Y) := by
    exact And.intro hxA (Set.mem_univ y)
  have h_closure_mem : (x, y) ∈ closure (interior (A ×ˢ (Set.univ : Set Y))) :=
    hProd h_mem_prod
  have h_int_prod :
      interior (A ×ˢ (Set.univ : Set Y)) =
        interior A ×ˢ (Set.univ : Set Y) := by
    simpa using
      interior_prod_eq (s := A) (t := (Set.univ : Set Y))
  have h_closure_prod :
      closure (interior (A ×ˢ (Set.univ : Set Y))) =
        closure (interior A) ×ˢ (Set.univ : Set Y) := by
    calc
      closure (interior (A ×ˢ (Set.univ : Set Y)))
          = closure (interior A ×ˢ (Set.univ : Set Y)) := by
              simpa [h_int_prod]
      _ = closure (interior A) ×ˢ (Set.univ : Set Y) := by
              simpa using
                closure_prod_eq
                  (s := interior A) (t := (Set.univ : Set Y))
  have h_in_prod :
      (x, y) ∈ closure (interior A) ×ˢ (Set.univ : Set Y) := by
    simpa [h_closure_prod] using h_closure_mem
  exact (Set.mem_prod.1 h_in_prod).1

theorem P3_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Topology.P3 ((Set.univ : Set X) ×ˢ B) → Topology.P3 B := by
  intro hProd
  dsimp [Topology.P3] at hProd
  dsimp [Topology.P3]
  intro y hyB
  classical
  -- pick an arbitrary element of `X`
  have x : X := Classical.arbitrary X
  -- the point `(x, y)` lies in the product set
  have h_mem_prod : ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ B := by
    exact And.intro (by trivial) hyB
  -- apply the `P3` property of the product
  have h_int_prod :
      ((x, y) : X × Y) ∈ interior (closure ((Set.univ : Set X) ×ˢ B)) :=
    hProd h_mem_prod
  -- identify the closure of the product
  have h_closure_prod :
      closure ((Set.univ : Set X) ×ˢ B) =
        (Set.univ : Set X) ×ˢ closure B := by
    simpa [closure_univ] using
      closure_prod_eq (s := (Set.univ : Set X)) (t := B)
  -- rewrite membership using the equality above
  have h_int_prod' :
      ((x, y) : X × Y) ∈ interior ((Set.univ : Set X) ×ˢ closure B) := by
    simpa [h_closure_prod] using h_int_prod
  -- identify the interior of the product
  have h_int_eq :
      interior ((Set.univ : Set X) ×ˢ closure B) =
        (Set.univ : Set X) ×ˢ interior (closure B) := by
    simpa [interior_univ] using
      interior_prod_eq (s := (Set.univ : Set X)) (t := closure B)
  -- transport membership through this last equality
  have h_final :
      ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ interior (closure B) := by
    simpa [h_int_eq] using h_int_prod'
  -- extract the `Y`-coordinate
  exact (Set.mem_prod.1 h_final).2

theorem P1_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Topology.P1 ((Set.univ : Set X) ×ˢ B) → Topology.P1 B := by
  intro hProd
  dsimp [Topology.P1] at hProd
  dsimp [Topology.P1]
  intro y hyB
  classical
  have x : X := Classical.arbitrary X
  have h_mem_prod : ((x, y) : X × Y) ∈ ((Set.univ : Set X) ×ˢ B) := by
    exact And.intro (by trivial) hyB
  have h_closure_mem :
      ((x, y) : X × Y) ∈ closure (interior ((Set.univ : Set X) ×ˢ B)) :=
    hProd h_mem_prod
  have h_int_prod :
      interior ((Set.univ : Set X) ×ˢ B) =
        (Set.univ : Set X) ×ˢ interior B := by
    simpa [interior_univ] using
      interior_prod_eq (s := (Set.univ : Set X)) (t := B)
  have h_closure_prod :
      closure (interior ((Set.univ : Set X) ×ˢ B)) =
        (Set.univ : Set X) ×ˢ closure (interior B) := by
    calc
      closure (interior ((Set.univ : Set X) ×ˢ B))
          = closure ((Set.univ : Set X) ×ˢ interior B) := by
            simpa [h_int_prod]
      _ = closure (Set.univ : Set X) ×ˢ closure (interior B) := by
            simpa [closure_univ] using
              closure_prod_eq (s := (Set.univ : Set X)) (t := interior B)
      _ = (Set.univ : Set X) ×ˢ closure (interior B) := by
            simpa [closure_univ]
  have h_mem_prod_closure :
      ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ closure (interior B) := by
    simpa [h_closure_prod] using h_closure_mem
  exact (Set.mem_prod.1 h_mem_prod_closure).2

theorem P2_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Topology.P2 (A ×ˢ (Set.univ : Set Y)) → Topology.P2 A := by
  intro hProd
  dsimp [Topology.P2] at hProd ⊢
  intro x hxA
  classical
  -- Choose an arbitrary element of `Y` to form a point in the product.
  let y : Y := Classical.arbitrary Y
  have h_mem_prod : (x, y) ∈ A ×ˢ (Set.univ : Set Y) := by
    exact ⟨hxA, Set.mem_univ y⟩
  -- Apply the `P2` property of the product.
  have h_int_prod :
      (x, y) ∈ interior (closure (interior (A ×ˢ (Set.univ : Set Y)))) :=
    hProd h_mem_prod
  -- Identify `interior (A ×ˢ univ)` with a product of interiors.
  have h_int_prod_eq :
      interior (A ×ˢ (Set.univ : Set Y)) =
        interior A ×ˢ (Set.univ : Set Y) := by
    simpa [interior_univ] using
      interior_prod_eq (s := A) (t := (Set.univ : Set Y))
  -- Identify `closure` of this interior with a product of closures.
  have h_closure_prod :
      closure (interior (A ×ˢ (Set.univ : Set Y))) =
        closure (interior A) ×ˢ (Set.univ : Set Y) := by
    calc
      closure (interior (A ×ˢ (Set.univ : Set Y)))
          = closure (interior A ×ˢ (Set.univ : Set Y)) := by
              simpa [h_int_prod_eq]
      _ = closure (interior A) ×ˢ (Set.univ : Set Y) := by
              simpa [closure_univ] using
                closure_prod_eq
                  (s := interior A) (t := (Set.univ : Set Y))
  -- Rewrite the interior of this closure.
  have h_interior_closure_prod :
      interior (closure (interior (A ×ˢ (Set.univ : Set Y)))) =
        interior (closure (interior A)) ×ˢ (Set.univ : Set Y) := by
    calc
      interior (closure (interior (A ×ˢ (Set.univ : Set Y))))
          = interior ((closure (interior A)) ×ˢ (Set.univ : Set Y)) := by
              simpa [h_closure_prod]
      _ = interior (closure (interior A)) ×ˢ (Set.univ : Set Y) := by
              simpa [interior_univ] using
                interior_prod_eq
                  (s := closure (interior A)) (t := (Set.univ : Set Y))
  -- Transport membership through these identities.
  have h_prod_mem' :
      (x, y) ∈
        interior (closure (interior A)) ×ˢ (Set.univ : Set Y) := by
    simpa [h_interior_closure_prod] using h_int_prod
  -- Extract the `X`-coordinate to conclude.
  exact (Set.mem_prod.1 h_prod_mem').1

theorem P2_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Topology.P2 ((Set.univ : Set X) ×ˢ B) → Topology.P2 B := by
  intro hProd
  dsimp [Topology.P2] at hProd ⊢
  intro y hyB
  classical
  -- Choose an arbitrary element of `X` to form a point in the product.
  have x : X := Classical.arbitrary X
  have h_mem_prod : ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ B :=
    by exact And.intro (by trivial) hyB
  -- Apply the `P2` property of the product set.
  have h_int_prod :
      ((x, y) : X × Y) ∈ interior (closure (interior ((Set.univ : Set X) ×ˢ B))) :=
    hProd h_mem_prod
  -- Identify `interior ((univ) ×ˢ B)` with a product of interiors.
  have h_int_eq :
      interior ((Set.univ : Set X) ×ˢ B) =
        (Set.univ : Set X) ×ˢ interior B := by
    simpa [interior_univ] using
      interior_prod_eq (s := (Set.univ : Set X)) (t := B)
  -- Identify the closure of this interior with a product of closures.
  have h_closure_eq :
      closure (interior ((Set.univ : Set X) ×ˢ B)) =
        (Set.univ : Set X) ×ˢ closure (interior B) := by
    have :
        closure ((Set.univ : Set X) ×ˢ interior B) =
          closure (Set.univ : Set X) ×ˢ closure (interior B) := by
      simpa using
        closure_prod_eq (s := (Set.univ : Set X)) (t := interior B)
    simpa [h_int_eq, closure_univ] using this
  -- Rewrite the interior of this closure.
  have h_interior_closure_eq :
      interior (closure (interior ((Set.univ : Set X) ×ˢ B))) =
        (Set.univ : Set X) ×ˢ interior (closure (interior B)) := by
    have :
        interior ((Set.univ : Set X) ×ˢ closure (interior B)) =
          (Set.univ : Set X) ×ˢ interior (closure (interior B)) := by
      simpa [interior_univ] using
        interior_prod_eq (s := (Set.univ : Set X)) (t := closure (interior B))
    simpa [h_closure_eq] using this
  -- Transport membership through these identities.
  have h_mem_prod_int :
      ((x, y) : X × Y) ∈
        (Set.univ : Set X) ×ˢ interior (closure (interior B)) := by
    simpa [h_interior_closure_eq] using h_int_prod
  -- Extract the `Y`-coordinate to conclude.
  exact (Set.mem_prod.1 h_mem_prod_int).2

theorem P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ :=
    (Topology.P2_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := A))
  have h₂ :=
    (Topology.P3_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := A))
  simpa using h₁.trans h₂.symm

theorem P3_prod_implies_P3_left_and_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hProd : Topology.P3 (A ×ˢ B))
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P3 A ∧ Topology.P3 B := by
  -- First, derive `P3 A`.
  have hP3A : Topology.P3 A := by
    dsimp [Topology.P3] at hProd
    dsimp [Topology.P3]
    intro x hx
    rcases hBne with ⟨y, hy⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hx, hy⟩
    have h_int_prod : ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) :=
      hProd h_mem_prod
    -- Rewrite the interior of the closure of the product.
    have h_closure_prod :
        closure (A ×ˢ B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq (s := A) (t := B)
    have h_int_prod' :
        ((x, y) : X × Y) ∈
          interior ((closure A) ×ˢ (closure B)) := by
      simpa [h_closure_prod] using h_int_prod
    have h_int_eq :
        interior ((closure A) ×ˢ (closure B)) =
          interior (closure A) ×ˢ interior (closure B) := by
      simpa using interior_prod_eq (s := closure A) (t := closure B)
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure A) ×ˢ interior (closure B) := by
      simpa [h_int_eq] using h_int_prod'
    exact (Set.mem_prod.1 h_mem).1
  -- Next, derive `P3 B`.
  have hP3B : Topology.P3 B := by
    dsimp [Topology.P3] at hProd
    dsimp [Topology.P3]
    intro y hy
    rcases hAne with ⟨x, hx⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hx, hy⟩
    have h_int_prod : ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) :=
      hProd h_mem_prod
    -- Rewrite as above.
    have h_closure_prod :
        closure (A ×ˢ B) = closure A ×ˢ closure B := by
      simpa using closure_prod_eq (s := A) (t := B)
    have h_int_prod' :
        ((x, y) : X × Y) ∈
          interior ((closure A) ×ˢ (closure B)) := by
      simpa [h_closure_prod] using h_int_prod
    have h_int_eq :
        interior ((closure A) ×ˢ (closure B)) =
          interior (closure A) ×ˢ interior (closure B) := by
      simpa using interior_prod_eq (s := closure A) (t := closure B)
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure A) ×ˢ interior (closure B) := by
      simpa [h_int_eq] using h_int_prod'
    exact (Set.mem_prod.1 h_mem).2
  exact ⟨hP3A, hP3B⟩

theorem P1_prod_implies_P1_left_and_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hProd : Topology.P1 (A ×ˢ B))
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P1 A ∧ Topology.P1 B := by
  -- First derive `P1 A`
  have hP1A : Topology.P1 A := by
    dsimp [Topology.P1] at hProd ⊢
    intro x hxA
    -- Choose an element of `B` to form a point in the product.
    rcases hBne with ⟨y, hyB⟩
    have hxy_mem : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply `P1` to the product.
    have h_cl_prod : ((x, y) : X × Y) ∈ closure (interior (A ×ˢ B)) :=
      hProd hxy_mem
    -- Rewrite the relevant closures using product rules.
    have h_int_prod :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    -- Extract the `X`-coordinate.
    have h_mem :
        ((x, y) : X × Y) ∈
          closure (interior A) ×ˢ closure (interior B) := by
      simpa [h_closure_prod] using h_cl_prod
    exact (Set.mem_prod.1 h_mem).1
  -- Next derive `P1 B`
  have hP1B : Topology.P1 B := by
    dsimp [Topology.P1] at hProd ⊢
    intro y hyB
    -- Choose an element of `A` to form a point in the product.
    rcases hAne with ⟨x, hxA⟩
    have hxy_mem : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply `P1` to the product.
    have h_cl_prod : ((x, y) : X × Y) ∈ closure (interior (A ×ˢ B)) :=
      hProd hxy_mem
    -- Rewrite closures as above.
    have h_int_prod :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    -- Extract the `Y`-coordinate.
    have h_mem :
        ((x, y) : X × Y) ∈
          closure (interior A) ×ˢ closure (interior B) := by
      simpa [h_closure_prod] using h_cl_prod
    exact (Set.mem_prod.1 h_mem).2
  exact ⟨hP1A, hP1B⟩

theorem P2_prod_implies_P2_left_and_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hProd : Topology.P2 (A ×ˢ B))
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P2 A ∧ Topology.P2 B := by
  -- First, derive `P2 A`.
  have hP2A : Topology.P2 A := by
    dsimp [Topology.P2] at hProd ⊢
    intro x hxA
    -- Choose a witness in `B` to build a point in the product.
    rcases hBne with ⟨y, hyB⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply the `P2` property to the product.
    have h_int_prod : ((x, y) : X × Y) ∈
        interior (closure (interior (A ×ˢ B))) := hProd h_mem_prod
    -- Rewrite the relevant interiors and closures.
    have h_int_prod_eq :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod_eq]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    have h_interior_closure_prod :
        interior (closure (interior (A ×ˢ B))) =
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      calc
        interior (closure (interior (A ×ˢ B)))
            = interior ((closure (interior A)) ×ˢ (closure (interior B))) := by
                simpa [h_closure_prod]
        _ = interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
                simpa using
                  interior_prod_eq
                    (s := closure (interior A))
                    (t := closure (interior B))
    -- Extract the `X`-coordinate from the membership.
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      simpa [h_interior_closure_prod] using h_int_prod
    exact (Set.mem_prod.1 h_mem).1
  -- Next, derive `P2 B`.
  have hP2B : Topology.P2 B := by
    dsimp [Topology.P2] at hProd ⊢
    intro y hyB
    -- Choose a witness in `A` to build a point in the product.
    rcases hAne with ⟨x, hxA⟩
    have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := ⟨hxA, hyB⟩
    -- Apply the `P2` property to the product.
    have h_int_prod : ((x, y) : X × Y) ∈
        interior (closure (interior (A ×ˢ B))) := hProd h_mem_prod
    -- Reuse the computations above (they remain valid).
    have h_int_prod_eq :
        interior (A ×ˢ B) = interior A ×ˢ interior B := by
      simpa using interior_prod_eq (s := A) (t := B)
    have h_closure_prod :
        closure (interior (A ×ˢ B)) =
          closure (interior A) ×ˢ closure (interior B) := by
      calc
        closure (interior (A ×ˢ B))
            = closure (interior A ×ˢ interior B) := by
                simpa [h_int_prod_eq]
        _ = closure (interior A) ×ˢ closure (interior B) := by
                simpa using
                  closure_prod_eq (s := interior A) (t := interior B)
    have h_interior_closure_prod :
        interior (closure (interior (A ×ˢ B))) =
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      calc
        interior (closure (interior (A ×ˢ B)))
            = interior ((closure (interior A)) ×ˢ (closure (interior B))) := by
                simpa [h_closure_prod]
        _ = interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
                simpa using
                  interior_prod_eq
                    (s := closure (interior A))
                    (t := closure (interior B))
    -- Extract the `Y`-coordinate from the membership.
    have h_mem :
        ((x, y) : X × Y) ∈
          interior (closure (interior A)) ×ˢ
            interior (closure (interior B)) := by
      simpa [h_interior_closure_prod] using h_int_prod
    exact (Set.mem_prod.1 h_mem).2
  exact ⟨hP2A, hP2B⟩

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hAne
  classical
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  have hAeq : A = (∅ : Set X) :=
    Topology.P1_imp_eq_empty_of_empty_interior
      (X := X) (A := A) hP1 hIntEq
  rcases hAne with ⟨x, hx⟩
  have : x ∈ (∅ : Set X) := by
    simpa [hAeq] using hx
  exact this.elim

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem P3_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P3 (A ×ˢ B) ↔ (Topology.P3 A ∧ Topology.P3 B) := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_implies_P3_left_and_right
        (X := X) (Y := Y) (A := A) (B := B) hProd hAne hBne)
  · rintro ⟨hP3A, hP3B⟩
    exact
      Topology.P3_prod (X := X) (Y := Y) (A := A) (B := B) hP3A hP3B

theorem P2_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P2 (A ×ˢ B) ↔ (Topology.P2 A ∧ Topology.P2 B) := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_implies_P2_left_and_right
        (X := X) (Y := Y) (A := A) (B := B) hProd hAne hBne)
  · rintro ⟨hP2A, hP2B⟩
    exact
      Topology.P2_prod (X := X) (Y := Y) (A := A) (B := B) hP2A hP2B

theorem P1_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P1 (A ×ˢ B) ↔ (Topology.P1 A ∧ Topology.P1 B) := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_implies_P1_left_and_right
        (X := X) (Y := Y) (A := A) (B := B) hProd hAne hBne)
  · rintro ⟨hP1A, hP1B⟩
    exact
      Topology.P1_prod (X := X) (Y := Y) (A := A) (B := B) hP1A hP1B

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} :
    Topology.P3 A → Topology.P3 (A ×ˢ (Set.univ : Set Y)) := by
  intro hA
  have hUniv : Topology.P3 (Set.univ : Set Y) := Topology.P3_univ (X := Y)
  exact
    Topology.P3_prod
      (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} :
    Topology.P2 A → Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP2A
  have hP2Univ : Topology.P2 (Set.univ : Set Y) :=
    Topology.P2_univ (X := Y)
  exact
    Topology.P2_prod
      (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y))
      hP2A hP2Univ

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} :
    Topology.P1 A → Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro hA
  have hUniv : Topology.P1 (Set.univ : Set Y) :=
    Topology.P1_univ (X := Y)
  exact
    Topology.P1_prod
      (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y)) hA hUniv

theorem interior_closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ B)` is contained in both `closure A` and `closure B`
  have hA : closure (A ∩ B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : closure (A ∩ B) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  -- hence their interiors enjoy the same inclusion
  have hIntA : interior (closure (A ∩ B)) ⊆ interior (closure A) :=
    interior_mono hA
  have hIntB : interior (closure (A ∩ B)) ⊆ interior (closure B) :=
    interior_mono hB
  exact ⟨hIntA hx, hIntB hx⟩

theorem P1_implies_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (Topology.P2 A ↔ Topology.P3 A) := by
  intro hP1
  -- Thanks to `P1`, the two closures coincide.
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  constructor
  · -- `P2 A → P3 A` is always true.
    intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2
  · -- Under `P1`, `P3 A` implies `P2 A`.
    intro hP3
    dsimp [Topology.P2]
    intro x hxA
    -- From `P3`, the point lies in `interior (closure A)`.
    have hx_int_clA : x ∈ interior (closure A) := hP3 hxA
    -- Rewrite via the closure equality supplied by `P1`.
    have hx_int : x ∈ interior (closure (interior A)) := by
      simpa [h_closure_eq] using hx_int_clA
    exact hx_int

theorem P3_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} :
    Topology.P3 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P3 A := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_left
        (X := X) (Y := Y) (A := A)) hProd
  · intro hA
    exact
      (Topology.P3_prod_univ
        (X := X) (Y := Y) (A := A)) hA

theorem P2_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} :
    Topology.P2 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P2 A := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_left
        (X := X) (Y := Y) (A := A)) hProd
  · intro hA
    exact
      (Topology.P2_prod_univ
        (X := X) (Y := Y) (A := A)) hA

theorem P1_closure_iff_eq_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (closure A) ↔ closure A = closure (interior (closure A)) := by
  simpa [closure_closure] using
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := closure A))

theorem P1_prod_univ_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty Y] {A : Set X} :
    Topology.P1 (A ×ˢ (Set.univ : Set Y)) ↔ Topology.P1 A := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_left
        (X := X) (Y := Y) (A := A)) hProd
  · intro hA
    exact
      (Topology.P1_prod_univ
        (X := X) (Y := Y) (A := A)) hA

theorem P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ interior (closure A) := by
  intro hP2
  -- From `P2` we immediately obtain `P3`.
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Unpack the definition of `P3`.
  simpa [Topology.P3] using hP3

theorem subset_interiorClosure_of_subset_P3 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP3B : Topology.P3 B) :
    A ⊆ interior (closure B) := by
  intro x hxA
  -- Since `A ⊆ B`, the point `x` belongs to `B`.
  have hxB : x ∈ B := hAB hxA
  -- Apply the `P3` property of `B`.
  exact hP3B hxB

theorem closure_interior_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- Handle the case `x ∈ closure (interior A)`
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        -- `interior A ⊆ interior (A ∪ B)`
        have hIntSubset : interior A ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        -- Taking closures preserves inclusion
        exact closure_mono hIntSubset
      exact h_subset hA
  | inr hB =>
      -- Handle the case `x ∈ closure (interior B)`
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        -- `interior B ⊆ interior (A ∪ B)`
        have hIntSubset : interior B ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        -- Taking closures preserves inclusion
        exact closure_mono hIntSubset
      exact h_subset hB

theorem P3_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Topology.P3 (A ×ˢ B) → Topology.P3 A := by
  intro hProd
  dsimp [Topology.P3] at hProd
  dsimp [Topology.P3]
  intro x hxA
  rcases hBne with ⟨y, hyB⟩
  have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  have hIntProd : ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) :=
    hProd h_mem_prod
  have h_closure_prod :
      closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
    simpa using closure_prod_eq (s := A) (t := B)
  have hIntProd' :
      ((x, y) : X × Y) ∈ interior ((closure A) ×ˢ (closure B)) := by
    simpa [h_closure_prod] using hIntProd
  have h_int_prod_eq :
      interior ((closure A) ×ˢ (closure B)) =
        interior (closure A) ×ˢ interior (closure B) := by
    simpa using interior_prod_eq (s := closure A) (t := closure B)
  have hMem :
      ((x, y) : X × Y) ∈ interior (closure A) ×ˢ interior (closure B) := by
    simpa [h_int_prod_eq] using hIntProd'
  exact (Set.mem_prod.1 hMem).1

theorem closure_union_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  open Set in
  have h_subset : interior A ∪ interior B ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        have hMono : interior A ⊆ interior (A ∪ B) :=
          interior_mono (subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact hMono hA
    | inr hB =>
        have hMono : interior B ⊆ interior (A ∪ B) :=
          interior_mono (subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact hMono hB
  exact closure_mono h_subset

theorem closure_eq_univ_of_P1_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hDenseInt : Dense (interior A)) :
    closure A = (Set.univ : Set X) := by
  -- From `P1`, we know `closure A = closure (interior A)`.
  have h_cl_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Since `interior A` is dense, its closure is the whole space.
  have h_univ : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDenseInt.closure_eq
  -- Combining the two equalities yields the result.
  simpa [h_univ] using h_cl_eq

theorem P3_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} :
    Topology.P3 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P3 B := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_right (X := X) (Y := Y) (B := B)) hProd
  · intro hB
    have hUniv : Topology.P3 (Set.univ : Set X) := Topology.P3_univ (X := X)
    have h := Topology.P3_prod
        (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB
    simpa using h

theorem P3_closure_iff_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ interior (closure A) = closure A := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_interior_eq (X := X) (A := closure A) h_closed)

theorem closure_interior_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure (interior (A ×ˢ B)) = closure (interior A) ×ˢ closure (interior B) := by
  have h : interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  calc
    closure (interior (A ×ˢ B))
        = closure (interior A ×ˢ interior B) := by
          simpa [h]
    _ = closure (interior A) ×ˢ closure (interior B) := by
          simpa using closure_prod_eq (s := interior A) (t := interior B)

theorem P2_implies_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ↔ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact ⟨fun _ => hP3, fun _ => hP1⟩

theorem interior_dense_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ closure (interior A) = (Set.univ : Set X) := by
  simpa using (dense_iff_closure_eq (s := interior A))

theorem P2_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} :
    Topology.P2 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P2 B := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_right
        (X := X) (Y := Y) (B := B)) hProd
  · intro hB
    have hUniv : Topology.P2 (Set.univ : Set X) := Topology.P2_univ (X := X)
    simpa using
      (Topology.P2_prod
        (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)

theorem P1_univ_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] {B : Set Y} :
    Topology.P1 ((Set.univ : Set X) ×ˢ B) ↔ Topology.P1 B := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_right (X := X) (Y := Y) (B := B)) hProd
  · intro hB
    have hUniv : Topology.P1 (Set.univ : Set X) := Topology.P1_univ (X := X)
    have hProd :=
      Topology.P1_prod
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B) hUniv hB
    simpa using hProd

theorem denseInterior_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 (closure A) := by
  intro hDense
  dsimp [Topology.P1]
  intro x hx
  -- `closure (interior A)` is the whole space
  have h_closure_eq : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- hence `x` belongs to `closure (interior A)`
  have hx_intA : x ∈ closure (interior A) := by
    have : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [h_closure_eq] using this
  -- `interior A` is contained in `interior (closure A)`
  have h_int_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- taking closures preserves inclusion
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_intA

theorem closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`
  have h_sub : interior (closure A) ⊆ closure A := interior_subset
  -- Taking closures preserves inclusion
  have h_closure : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h_sub
  -- Simplify `closure (closure A)` to `closure A`
  simpa [closure_closure] using h_closure

theorem P1_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP1A : Topology.P1 A) (hBsubset : B ⊆ closure (interior A)) :
    Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at hP1A ⊢
  intro x hx_union
  -- We need to show that `x` belongs to `closure (interior (A ∪ B))`.
  -- First, note that `interior A ⊆ interior (A ∪ B)`.
  have hIntSubset : interior A ⊆ interior (A ∪ B) := by
    have h_sub : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
    exact interior_mono h_sub
  -- Consequently, taking closures preserves the inclusion.
  have hClosMono : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono hIntSubset
  -- Now treat the two possible ways in which `x` can lie in `A ∪ B`.
  cases hx_union with
  | inl hxA =>
      -- Case `x ∈ A`: use `P1` for `A`.
      have hx_clA : x ∈ closure (interior A) := hP1A hxA
      exact hClosMono hx_clA
  | inr hxB =>
      -- Case `x ∈ B`: use the assumption `B ⊆ closure (interior A)`.
      have hx_clA : x ∈ closure (interior A) := hBsubset hxB
      exact hClosMono hx_clA

theorem denseInterior_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _hx
  -- `closure (interior A)` is the whole space
  have h_closure_intA : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A ⊆ interior (closure A)`
  have h_int_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- hence `closure (interior A) ⊆ closure (interior (closure A))`
  have h_closure_subset :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono h_int_subset
  -- Using the previous equality, this forces `closure (interior (closure A)) = univ`
  have h_closure_eq_univ :
      closure (interior (closure A)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; exact Set.mem_univ y
    · have : (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
        simpa [h_closure_intA] using h_closure_subset
      exact this
  -- Therefore its interior is also `univ`.
  have h_interior_univ :
      interior (closure (interior (closure A))) = (Set.univ : Set X) := by
    simpa [h_closure_eq_univ, interior_univ]
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior_univ] using this

theorem P2_imp_eq_empty_of_empty_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A)
    (hIntEmpty : interior (closure (interior A)) = (∅ : Set X)) :
    A = (∅ : Set X) := by
  dsimp [Topology.P2] at hP2
  apply Set.Subset.antisymm
  · intro x hx
    have : x ∈ interior (closure (interior A)) := hP2 hx
    simpa [hIntEmpty] using this
  · exact Set.empty_subset _

theorem interior_has_all_P {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ∧
      Topology.P2 (interior A) ∧
        Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  exact
    Topology.isOpen_has_all_P
      (X := X) (A := interior A) h_open

theorem P1_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior (closure A)) = closure A := by
  intro hP1
  -- From `P1`, we have `closure A = closure (interior A)`.
  have h_cl : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- We prove the desired equality by showing both inclusions.
  apply Set.Subset.antisymm
  · -- `closure (interior (closure A)) ⊆ closure A`
    exact
      Topology.closure_interior_closure_subset_closure
        (X := X) (A := A)
  · -- `closure A ⊆ closure (interior (closure A))`
    -- Rewrite the left‐hand side via `h_cl`.
    have h_sub :
        closure (interior A) ⊆ closure (interior (closure A)) := by
      have h_int_sub :
          interior A ⊆ interior (closure A) :=
        Topology.interior_subset_interior_closure (X := X) (A := A)
      exact closure_mono h_int_sub
    simpa [h_cl] using h_sub

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  exact Set.empty_subset _

theorem P2_implies_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A = closure (interior (closure A)) := by
  intro hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact
    Topology.P3_implies_closure_eq_closure_interior_closure
      (X := X) (A := A) hP3

theorem interior_closure_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP1 hAne
  -- First, show that `interior A` is nonempty.
  have hInt_nonempty : (interior A).Nonempty := by
    by_contra hIntEmpty
    have hIntEq : interior A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hIntEmpty
    -- From `P1` and the emptiness of `interior A`, deduce `A = ∅`, contradiction.
    have hAEq : (A : Set X) = (∅ : Set X) :=
      Topology.P1_imp_eq_empty_of_empty_interior
        (X := X) (A := A) hP1 hIntEq
    rcases hAne with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hAEq] using hx
    exact this.elim
  -- Pick a point of `interior A`.
  rcases hInt_nonempty with ⟨x, hxInt⟩
  -- `interior A ⊆ interior (closure A)` by monotonicity.
  have hSubset : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  exact ⟨x, hSubset hxInt⟩

theorem P2_union_implies_P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P1 (A ∪ B) := by
  intro hP2A hP2B
  -- From `P2` we derive `P1` for each set.
  have hP1A : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2A
  have hP1B : Topology.P1 B :=
    Topology.P2_implies_P1 (X := X) (A := B) hP2B
  -- The union of two `P1` sets again satisfies `P1`.
  exact
    Topology.P1_union (X := X) (A := A) (B := B) hP1A hP1B

theorem closure_interior_closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (closure_interior_closure_interior_closure_eq
      (X := X) (A := closure A))

theorem P3_and_closure_eq_closure_interior_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior A) → Topology.P2 A := by
  intro hP3 hEq
  have hAnd : Topology.P3 A ∧ closure A = closure (interior A) := ⟨hP3, hEq⟩
  exact
    ((Topology.P2_iff_P3_and_closure_eq_closure_interior
        (X := X) (A := A)).2 hAnd)

theorem interior_closure_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior (closure (A ×ˢ B)) = interior (closure A) ×ˢ interior (closure B) := by
  have h₁ : closure (A ×ˢ B) = closure A ×ˢ closure B := by
    simpa using closure_prod_eq (s := A) (t := B)
  have h₂ :
      interior ((closure A) ×ˢ (closure B)) =
        interior (closure A) ×ˢ interior (closure B) := by
    simpa using interior_prod_eq (s := closure A) (t := closure B)
  simpa [h₁, h₂]



theorem P2_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Topology.P2 (A ×ˢ B) → Topology.P2 A := by
  intro hProd
  dsimp [Topology.P2] at hProd ⊢
  intro x hxA
  classical
  obtain ⟨y, hyB⟩ := hBne
  -- Form the point `(x, y)` in the product.
  have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  -- Apply the `P2` property of the product.
  have h_int_prod :
      ((x, y) : X × Y) ∈ interior (closure (interior (A ×ˢ B))) :=
    hProd h_mem_prod
  -- Identify `interior (A ×ˢ B)` with a product of interiors.
  have h_int_eq :
      interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  -- Identify the closure of this interior with a product of closures.
  have h_closure_eq :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) := by
    calc
      closure (interior (A ×ˢ B))
          = closure (interior A ×ˢ interior B) := by
              simpa [h_int_eq]
      _ = closure (interior A) ×ˢ closure (interior B) := by
              simpa using
                closure_prod_eq (s := interior A) (t := interior B)
  -- Rewrite the relevant interior once more.
  have h_interior_closure_eq :
      interior (closure (interior (A ×ˢ B))) =
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    calc
      interior (closure (interior (A ×ˢ B)))
          = interior ((closure (interior A)) ×ˢ (closure (interior B))) := by
              simpa [h_closure_eq]
      _ = interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
              simpa using
                interior_prod_eq
                  (s := closure (interior A))
                  (t := closure (interior B))
  -- Transport membership through these identifications and extract the `X`–coordinate.
  have h_mem :
      ((x, y) : X × Y) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    simpa [h_interior_closure_eq] using h_int_prod
  exact (Set.mem_prod.1 h_mem).1

theorem P2_closed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- Translate `P2` for a closed set into openness.
  have hOpen : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP2
  -- Open sets satisfy `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem interior_closure_interior_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    interior (closure (interior A)) = (Set.univ : Set X) := by
  have h_closure : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_closure, interior_univ]

theorem interior_closure_union_subset_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have : closure A ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact h_mono hA
  | inr hB =>
      have h_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have : closure B ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        exact interior_mono this
      exact h_mono hB

theorem closureInterior_prod_subset_closureInterior_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure (interior A) ×ˢ closure (interior B) ⊆
      closure (interior (A ×ˢ B)) := by
  intro z hz
  have h_eq :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) :=
    closure_interior_prod (X := X) (Y := Y) (A := A) (B := B)
  simpa [h_eq] using hz

theorem denseInterior_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure A) := by
  intro hDense
  -- First obtain `P2 (closure A)` from the density of `interior A`.
  have hP2 : Topology.P2 (closure A) :=
    Topology.denseInterior_implies_P2_closure (X := X) (A := A) hDense
  -- Use the equivalence between `P2` and `P3` for a closed set.
  have hEquiv :=
    (Topology.P2_closure_iff_P3_closure (X := X) (A := A))
  -- Convert `P2` into `P3`.
  exact hEquiv.1 hP2

theorem closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- `interior (A ∩ B)` is contained in both `interior A` and `interior B`
  have hA : interior (A ∩ B : Set X) ⊆ interior A := by
    have : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact interior_mono this
  have hB : interior (A ∩ B : Set X) ⊆ interior B := by
    have : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact interior_mono this
  -- Taking closures preserves these inclusions
  have hA' : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hA
  have hB' : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hB
  exact ⟨hA' hx, hB' hx⟩

theorem P2_iff_P3_of_closure_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : closure A = closure (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ :=
    (Topology.P2_iff_P3_and_closure_eq_closure_interior
      (X := X) (A := A))
  have h₂ :
      (Topology.P3 A ∧ closure A = closure (interior A)) ↔
        Topology.P3 A := by
    constructor
    · intro h; exact h.1
    · intro hP3; exact And.intro hP3 hEq
  exact h₁.trans h₂

theorem P1_subset_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior (closure A)) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  intro x hxA
  -- From `P1`, the point `x` lies in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
  have h_int_subset : interior A ⊆ interior (closure A) := by
    have : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono this
  -- Taking closures preserves inclusion.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_int_subset
  exact h_closure_subset hx_cl

theorem interior_closure_prod_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior (closure A) ×ˢ interior (closure B) ⊆
      interior (closure (A ×ˢ B)) := by
  intro z hz
  have hEq :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  simpa [hEq] using hz

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _

theorem dense_left_and_P3_right_implies_P3_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hDense : Dense A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) := by
  dsimp [Topology.P3] at hP3B ⊢
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- `interior (closure A)` is the whole space, thanks to the density of `A`.
  have h_closureA : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  have h_int_closureA : interior (closure A) = (Set.univ : Set X) := by
    have : interior (closure A) = interior ((Set.univ : Set X)) := by
      simpa [h_closureA]
    simpa [interior_univ] using this
  -- Coordinates belong to the corresponding interiors.
  have hx : p.1 ∈ interior (closure A) := by
    have : p.1 ∈ (Set.univ : Set X) := by
      trivial
    simpa [h_int_closureA] using this
  have hy : p.2 ∈ interior (closure B) := hP3B hpB
  -- Relate `interior (closure (A ×ˢ B))` to a product of interiors.
  have h_closure_prod :
      closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
    simpa using closure_prod_eq (s := A) (t := B)
  have h_int_prod :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) := by
    have h := interior_prod_eq (s := closure A) (t := closure B)
    simpa [h_closure_prod] using h
  -- Assemble the conclusion.
  have h_mem : (p : X × Y) ∈
      interior (closure A) ×ˢ interior (closure B) := by
    exact And.intro hx hy
  simpa [h_int_prod] using h_mem

theorem P2_closure_interior_closure_iff_isOpen_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  simpa using
    (Topology.P2_closure_interior_iff_isOpen_closure_interior
      (X := X) (A := closure A))

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `x` lies in `interior A`
      have h_open : IsOpen (interior A) := isOpen_interior
      have h_nhds : interior A ∈ 𝓝 x := h_open.mem_nhds hA
      have h_sub : interior A ⊆ A ∪ B := by
        intro y hy
        exact Or.inl (interior_subset hy)
      have h_union : A ∪ B ∈ 𝓝 x := Filter.mem_of_superset h_nhds h_sub
      exact (mem_interior_iff_mem_nhds).2 h_union
  | inr hB =>
      -- `x` lies in `interior B`
      have h_open : IsOpen (interior B) := isOpen_interior
      have h_nhds : interior B ∈ 𝓝 x := h_open.mem_nhds hB
      have h_sub : interior B ⊆ A ∪ B := by
        intro y hy
        exact Or.inr (interior_subset hy)
      have h_union : A ∪ B ∈ 𝓝 x := Filter.mem_of_superset h_nhds h_sub
      exact (mem_interior_iff_mem_nhds).2 h_union

theorem closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : closure (A ∩ B : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : closure (A ∩ B : Set X) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨hA hx, hB hx⟩

theorem P1_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Topology.P1 (A ×ˢ B) → Topology.P1 A := by
  intro hProd
  dsimp [Topology.P1] at hProd ⊢
  intro x hxA
  classical
  -- Choose any element of `B` to build a point in the product.
  obtain ⟨y, hyB⟩ := hBne
  have h_mem_prod : ((x, y) : X × Y) ∈ A ×ˢ B := by
    exact And.intro hxA hyB
  -- Apply `P1` to the product.
  have h_cl_prod : ((x, y) : X × Y) ∈ closure (interior (A ×ˢ B)) :=
    hProd h_mem_prod
  -- Rewrite the relevant closures using product rules.
  have h_int_prod :
      interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  have h_closure_prod :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) := by
    calc
      closure (interior (A ×ˢ B))
          = closure (interior A ×ˢ interior B) := by
              simpa [h_int_prod]
      _ = closure (interior A) ×ˢ closure (interior B) := by
              simpa using
                closure_prod_eq (s := interior A) (t := interior B)
  -- Extract the `X`-coordinate.
  have h_mem :
      ((x, y) : X × Y) ∈
        closure (interior A) ×ˢ closure (interior B) := by
    simpa [h_closure_prod] using h_cl_prod
  exact (Set.mem_prod.1 h_mem).1

theorem P1_and_denseInterior_implies_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense (interior A) → Dense A := by
  intro hP1 hDenseInt
  -- From `P1` and the density of `interior A` we know `closure A = univ`.
  have h_closure :
      closure A = (Set.univ : Set X) :=
    closure_eq_univ_of_P1_and_denseInterior
      (X := X) (A := A) hP1 hDenseInt
  -- Translate this equality into the desired `Dense A`.
  exact (dense_iff_closure_eq).2 h_closure

theorem dense_union_has_P3_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense B → Topology.P3 (A ∪ B) := by
  intro hDenseB
  simpa [Set.union_comm] using
    (dense_union_has_P3 (X := X) (A := B) (B := A) hDenseB)

theorem denseInterior_implies_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  -- `closure (interior A)` is the whole space by density.
  have h_closure_intA : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A ⊆ interior (closure A)`, hence the corresponding closures satisfy
  -- `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_subset :
      (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
    have h_int_subset : interior A ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (X := X) (A := A)
    have h_closure_subset :
        (closure (interior A) : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono h_int_subset
    simpa [h_closure_intA] using h_closure_subset
  -- Conclude the desired equality.
  apply Set.Subset.antisymm
  · intro x _; exact Set.mem_univ x
  · exact h_subset

theorem dense_right_and_P3_left_implies_P3_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hDenseB : Dense B) (hP3A : Topology.P3 A) :
    Topology.P3 (A ×ˢ B) := by
  -- Apply the existing lemma to the swapped product `B ×ˢ A`.
  have hSymm :
      Topology.P3 (B ×ˢ A) :=
    dense_left_and_P3_right_implies_P3_prod
      (X := Y) (Y := X) (A := B) (B := A) hDenseB hP3A
  -- Unfold the definition of `P3`.
  dsimp [Topology.P3] at hSymm ⊢
  intro p hp
  -- Use the result for the swapped point `(p.2, p.1)`.
  have hSwapped : (p.2, p.1) ∈ B ×ˢ A := And.intro hp.2 hp.1
  have hIntSwapped := hSymm hSwapped
  -- Identify the interiors of the relevant closures.
  have hEqSource :
      interior (closure (B ×ˢ A)) =
        interior (closure B) ×ˢ interior (closure A) :=
    interior_closure_prod (X := Y) (Y := X) (A := B) (B := A)
  have hEqTarget :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  -- Transport membership through `hEqSource`.
  have hMemSource :
      (p.2, p.1) ∈ interior (closure B) ×ˢ interior (closure A) := by
    simpa [hEqSource] using hIntSwapped
  -- Extract coordinate-wise information.
  have hpB : p.2 ∈ interior (closure B) := (Set.mem_prod.1 hMemSource).1
  have hpA : p.1 ∈ interior (closure A) := (Set.mem_prod.1 hMemSource).2
  -- Assemble the membership for the original point.
  have hMemTarget :
      (p.1, p.2) ∈ interior (closure A) ×ˢ interior (closure B) :=
    And.intro hpA hpB
  simpa [hEqTarget] using hMemTarget

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  exact Set.empty_subset _

theorem interior_nonempty_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hAne
  classical
  by_contra hInt
  have hIntEq : interior A = (∅ : Set X) :=
    (Set.not_nonempty_iff_eq_empty).1 hInt
  have hInnerEmpty : interior (closure (interior A)) = (∅ : Set X) := by
    simpa [hIntEq, closure_empty, interior_empty]
  rcases hAne with ⟨x, hx⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hx
  have : x ∈ (∅ : Set X) := by
    simpa [hInnerEmpty] using hxInt
  exact this.elim

theorem dense_prod_of_dense_left_and_dense_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : Dense A) (hB : Dense B) :
    Dense (A ×ˢ B) := by
  -- We show that the closure of `A ×ˢ B` is the whole space.
  have hClosure :
      closure (A ×ˢ B : Set (X × Y)) = (Set.univ : Set (X × Y)) := by
    calc
      closure (A ×ˢ B : Set (X × Y))
          = closure A ×ˢ closure B := by
            simpa using closure_prod_eq (s := A) (t := B)
      _ = (Set.univ : Set X) ×ˢ (Set.univ : Set Y) := by
        simpa [hA.closure_eq, hB.closure_eq]
      _ = (Set.univ : Set (X × Y)) := by
        simpa [Set.univ_prod_univ]
  -- Conclude density from the characterization via closures.
  exact (dense_iff_closure_eq).2 hClosure

theorem dense_prod_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Dense (A ×ˢ B) ↔ (Dense A ∧ Dense B) := by
  constructor
  · intro hDenseProd
    -- `closure (A ×ˢ B)` is the whole space.
    have hClosureProd :
        (closure (A ×ˢ B) : Set (X × Y)) = (Set.univ : Set (X × Y)) := by
      simpa using hDenseProd.closure_eq
    -- Identify `closure (A ×ˢ B)` via the product rule.
    have hProdClosure :
        (closure (A ×ˢ B) : Set (X × Y)) = closure A ×ˢ closure B := by
      simpa using (closure_prod_eq (s := A) (t := B))
    -- Hence the product of closures is `univ`.
    have hProdUniv :
        closure A ×ˢ closure B = (Set.univ : Set (X × Y)) := by
      calc
        closure A ×ˢ closure B
            = (closure (A ×ˢ B) : Set (X × Y)) := by
                symm; simpa using hProdClosure
        _ = (Set.univ : Set (X × Y)) := hClosureProd
    -- Deduce `closure A = univ`.
    have hClosureA : (closure (A : Set X)) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro x _; trivial
      · intro x _
        rcases hBne with ⟨y0, _hy0⟩
        have : ((x, y0) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        have : ((x, y0) : X × Y) ∈ closure A ×ˢ closure B := by
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).1
    -- Deduce `closure B = univ`.
    have hClosureB : (closure (B : Set Y)) = (Set.univ : Set Y) := by
      apply Set.Subset.antisymm
      · intro y _; trivial
      · intro y _
        rcases hAne with ⟨x0, _hx0⟩
        have : ((x0, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        have : ((x0, y) : X × Y) ∈ closure A ×ˢ closure B := by
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).2
    -- Conclude density of the factors.
    have hDenseA : Dense A := (dense_iff_closure_eq).2 hClosureA
    have hDenseB : Dense B := (dense_iff_closure_eq).2 hClosureB
    exact ⟨hDenseA, hDenseB⟩
  · rintro ⟨hDenseA, hDenseB⟩
    exact dense_prod_of_dense_left_and_dense_right hDenseA hDenseB

theorem closure_interior_closure_interior_closure_interior_has_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior (closure A))))) := by
  -- The set `interior (closure (interior (closure A)))` already has `P1`.
  have hInner :
      Topology.P1 (interior (closure (interior (closure A)))) :=
    Topology.interior_has_P1
      (X := X) (A := closure (interior (closure A)))
  -- Transfer `P1` through the closure operator.
  exact
    Topology.P1_implies_P1_closure
      (X := X)
      (A := interior (closure (interior (closure A))))
      hInner

theorem interior_prod_nonempty_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior (A ×ˢ B)).Nonempty ↔
      ((interior A).Nonempty ∧ (interior B).Nonempty) := by
  -- We use the characterization of the interior of a product.
  have h : interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  constructor
  · intro hNonempty
    rcases hNonempty with ⟨p, hp⟩
    have hp' : (p : X × Y) ∈ interior A ×ˢ interior B := by
      simpa [h] using hp
    rcases Set.mem_prod.1 hp' with ⟨hpA, hpB⟩
    exact ⟨⟨p.1, hpA⟩, ⟨p.2, hpB⟩⟩
  · rintro ⟨hIntA, hIntB⟩
    rcases hIntA with ⟨x, hx⟩
    rcases hIntB with ⟨y, hy⟩
    have hp : ((x, y) : X × Y) ∈ interior A ×ˢ interior B :=
      And.intro hx hy
    have : ((x, y) : X × Y) ∈ interior (A ×ˢ B) := by
      simpa [h] using hp
    exact ⟨(x, y), this⟩

theorem closure_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) :
    closure (A ×ˢ (Set.univ : Set Y)) = (closure A) ×ˢ (Set.univ : Set Y) := by
  simpa [closure_univ] using
    (closure_prod_eq (s := A) (t := (Set.univ : Set Y)))

theorem dense_prod_univ_left_of_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Dense (A ×ˢ (Set.univ : Set Y)) → Dense A := by
  intro hDenseProd
  -- We will show that `closure A = univ`, which implies `Dense A`.
  have h_closureA_univ : closure (A : Set X) = (Set.univ : Set X) := by
    -- The closure of the product is `univ`.
    have h_closure_prod_univ :
        closure (A ×ˢ (Set.univ : Set Y) : Set (X × Y)) =
          (Set.univ : Set (X × Y)) := by
      simpa using hDenseProd.closure_eq
    -- The closure of the product can also be written as a product of closures.
    have h_closure_prod :
        closure (A ×ˢ (Set.univ : Set Y) : Set (X × Y)) =
          closure (A : Set X) ×ˢ (Set.univ : Set Y) := by
      simpa [closure_univ] using
        (closure_prod_eq (s := A) (t := (Set.univ : Set Y)))
    -- Hence this product of closures is the whole space.
    have h_prod_eq_univ :
        closure (A : Set X) ×ˢ (Set.univ : Set Y) =
          (Set.univ : Set (X × Y)) :=
      (Eq.symm h_closure_prod).trans h_closure_prod_univ
    -- Prove the reverse inclusion `univ ⊆ closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      classical
      let y : Y := Classical.arbitrary Y
      have h_mem_univ : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
        trivial
      have h_mem_prod :
          ((x, y) : X × Y) ∈ closure (A : Set X) ×ˢ (Set.univ : Set Y) := by
        simpa [h_prod_eq_univ] using h_mem_univ
      exact (Set.mem_prod.1 h_mem_prod).1
    -- Assemble the set equality.
    apply Set.Subset.antisymm
    · -- `closure A ⊆ univ`
      intro _ _; trivial
    · exact h_univ_subset
  -- Conclude density from the characterization via closures.
  exact (dense_iff_closure_eq).2 h_closureA_univ

theorem P1_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior A) := by
  intro hP1
  simpa [Topology.P1] using hP1

theorem interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  have h_int : interior A ⊆ interior B := interior_mono hAB
  have h_closure : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int
  exact interior_mono h_closure

theorem interior_closure_prod_nonempty_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (interior (closure (A ×ˢ B))).Nonempty ↔
      ((interior (closure A)).Nonempty ∧ (interior (closure B)).Nonempty) := by
  have hEq :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  constructor
  · intro hProd
    rcases hProd with ⟨p, hp⟩
    have hp' :
        (p : X × Y) ∈ interior (closure A) ×ˢ interior (closure B) := by
      simpa [hEq] using hp
    rcases hp' with ⟨hpA, hpB⟩
    exact ⟨⟨p.1, hpA⟩, ⟨p.2, hpB⟩⟩
  · rintro ⟨hIntA, hIntB⟩
    rcases hIntA with ⟨x, hx⟩
    rcases hIntB with ⟨y, hy⟩
    have hp :
        ((x, y) : X × Y) ∈
          interior (closure A) ×ˢ interior (closure B) :=
      And.intro hx hy
    have hpProd :
        ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) := by
      simpa [hEq] using hp
    exact ⟨(x, y), hpProd⟩



theorem dense_prod_univ_right_of_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Dense ((Set.univ : Set X) ×ˢ B) → Dense B := by
  intro hDenseProd
  -- We show that `closure B = univ`, from which density follows.
  have h_closureB_univ : (closure (B : Set Y)) = (Set.univ : Set Y) := by
    -- First, the easy inclusion `closure B ⊆ univ`.
    have h₁ : (closure (B : Set Y)) ⊆ (Set.univ : Set Y) := by
      intro y _; trivial
    -- For the reverse inclusion, fix an arbitrary `y : Y`.
    have h₂ : (Set.univ : Set Y) ⊆ closure B := by
      intro y _hy
      classical
      -- Pick an arbitrary `x : X`.
      let x : X := Classical.arbitrary X
      -- The point `(x, y)` belongs to `univ`.
      have h_mem_univ : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
        trivial
      -- Since the product set is dense, its closure is `univ`.
      have h_closure_prod_univ :
          closure ((Set.univ : Set X) ×ˢ B : Set (X × Y)) =
            (Set.univ : Set (X × Y)) := by
        simpa using hDenseProd.closure_eq
      -- The closure of the product can also be written as a product of closures.
      have h_closure_prod :
          closure ((Set.univ : Set X) ×ˢ B : Set (X × Y)) =
            (Set.univ : Set X) ×ˢ closure (B : Set Y) := by
        simpa [closure_univ] using
          closure_prod_eq (s := (Set.univ : Set X)) (t := B)
      -- Transport the membership of `(x, y)` through these equalities.
      have h_mem_prod_closure :
          ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ closure (B : Set Y) := by
        -- `(x, y)` lies in the closure of the product...
        have h_in_closure :
            ((x, y) : X × Y) ∈
              closure ((Set.univ : Set X) ×ˢ B : Set (X × Y)) := by
          simpa [h_closure_prod_univ] using h_mem_univ
        -- ...and hence in the product of the closures.
        simpa [h_closure_prod] using h_in_closure
      -- Extract the `Y`–component to obtain `y ∈ closure B`.
      exact (Set.mem_prod.1 h_mem_prod_closure).2
    -- Assemble the equality of sets.
    exact Set.Subset.antisymm h₁ h₂
  -- Conclude density from the characterization via closures.
  exact (dense_iff_closure_eq).2 h_closureB_univ

theorem closure_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (B : Set Y) :
    closure ((Set.univ : Set X) ×ˢ B) = (Set.univ : Set X) ×ˢ closure B := by
  simpa [closure_univ] using
    (closure_prod_eq (s := (Set.univ : Set X)) (t := B))

theorem interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- First, enlarge `interior A` to `interior (closure A)`.
  have hx_int_closure : x ∈ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A) hx
  -- Then, any point of an open set belongs to the closure of that set.
  exact subset_closure hx_int_closure

theorem dense_prod_univ_left_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} :
    Dense (A ×ˢ (Set.univ : Set Y)) ↔ Dense A := by
  constructor
  · intro hDenseProd
    exact
      dense_prod_univ_left_of_dense
        (X := X) (Y := Y) (A := A) hDenseProd
  · intro hDenseA
    -- `Set.univ` is dense in `Y`.
    have hDenseUniv : Dense (Set.univ : Set Y) := by
      have h_closure : closure (Set.univ : Set Y) = (Set.univ : Set Y) := by
        simpa [closure_univ]
      exact (dense_iff_closure_eq).2 h_closure
    -- Combine the densities of the factors.
    exact
      dense_prod_of_dense_left_and_dense_right
        (X := X) (Y := Y) (A := A) (B := (Set.univ : Set Y))
        hDenseA hDenseUniv

theorem dense_implies_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (interior (closure A)) := by
  intro hDense
  -- From the density of `A` we know that `closure (interior (closure A)) = univ`.
  have h_closure_eq :
      closure (interior (closure A) : Set X) = (Set.univ : Set X) :=
    dense_closure_interior_closure_eq_univ (X := X) (A := A) hDense
  -- Translate this equality into density.
  exact (dense_iff_closure_eq).2 h_closure_eq

theorem denseInterior_closure_implies_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure A)) → Dense A := by
  intro hDense
  -- `closure (interior (closure A))` is the whole space.
  have h_closure_int_univ :
      (closure (interior (closure A) : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- We always have `closure (interior (closure A)) ⊆ closure A`.
  have h_subset :
      (closure (interior (closure A) : Set X)) ⊆ closure A :=
    closure_interior_closure_subset_closure (X := X) (A := A)
  -- Hence `closure A = univ`.
  have h_closureA_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · intro x _
      have hx : x ∈ closure (interior (closure A) : Set X) := by
        -- Reinterpret `x ∈ univ` using `h_closure_int_univ`.
        have : x ∈ (Set.univ : Set X) := by
          trivial
        simpa [h_closure_int_univ] using this
      exact h_subset hx
  -- Conclude the density of `A`.
  exact (dense_iff_closure_eq).2 h_closureA_univ

theorem P1_iff_P2_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro hP1
    exact Topology.P1_and_dense_implies_P2 (X := X) (A := A) hP1 hDense
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2

theorem P1_closure_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Topology.P1 A → Topology.P1 B →
      Topology.P1 (closure A ×ˢ closure B) := by
  intro hA hB
  -- First, upgrade the hypotheses to the closures of the factors.
  have hAc : Topology.P1 (closure A) :=
    Topology.P1_implies_P1_closure (X := X) (A := A) hA
  have hBc : Topology.P1 (closure B) :=
    Topology.P1_implies_P1_closure (X := Y) (A := B) hB
  -- Apply the product rule for `P1`.
  simpa using
    (Topology.P1_prod
        (X := X) (Y := Y)
        (A := closure A) (B := closure B) hAc hBc)

theorem P1_dense_iff_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (Dense A ↔ Dense (interior A)) := by
  intro hP1
  -- From `P1`, the two closures coincide.
  have h_cl_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Characterisations of density via closures.
  have hDenseA : Dense A ↔ closure A = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := A))
  have hDenseInt : Dense (interior A) ↔
      closure (interior A) = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := interior A))
  -- Use the common closure to relate the two densities.
  constructor
  · intro hDA
    have hClA : closure A = (Set.univ : Set X) := hDenseA.mp hDA
    have hClInt : closure (interior A) = (Set.univ : Set X) := by
      simpa [h_cl_eq] using hClA
    exact hDenseInt.mpr hClInt
  · intro hDInt
    have hClInt : closure (interior A) = (Set.univ : Set X) :=
      hDenseInt.mp hDInt
    have hClA : closure A = (Set.univ : Set X) := by
      simpa [h_cl_eq] using hClInt
    exact hDenseA.mpr hClA

theorem dense_iff_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ Dense (interior (closure A)) := by
  constructor
  · intro hDense
    exact
      dense_implies_dense_interior_closure (X := X) (A := A) hDense
  · intro hDenseInt
    exact
      denseInterior_closure_implies_dense (X := X) (A := A) hDenseInt

theorem interior_closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hDense : Dense A) :
    interior (closure (interior (closure A))) = (Set.univ : Set X) := by
  -- The density of `A` gives `closure A = univ`.
  have hClosure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Rewrite using `hClosure` and evaluate with `simp`.
  simpa [hClosure, closure_univ, interior_univ]

theorem interior_union_has_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∪ interior B) := by
  -- `interior A` and `interior B` each satisfy `P1`.
  have hP1A : Topology.P1 (interior A) :=
    Topology.interior_has_P1 (X := X) (A := A)
  have hP1B : Topology.P1 (interior B) :=
    Topology.interior_has_P1 (X := X) (A := B)
  -- The union of two `P1` sets again satisfies `P1`.
  exact
    Topology.P1_union
      (X := X) (A := interior A) (B := interior B) hP1A hP1B

theorem dense_prod_univ_right_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Dense ((Set.univ : Set X) ×ˢ B) ↔ Dense B := by
  constructor
  · intro hDenseProd
    exact
      dense_prod_univ_right_of_dense
        (X := X) (Y := Y) (B := B) hDenseProd
  · intro hDenseB
    -- `univ` is trivially dense.
    have hDenseUniv : Dense (Set.univ : Set X) := by
      simpa [closure_univ] using
        (dense_iff_closure_eq (s := (Set.univ : Set X))).2 rfl
    -- Combine the densities of the two factors.
    simpa using
      dense_prod_of_dense_left_and_dense_right
        (X := X) (Y := Y)
        (A := (Set.univ : Set X)) (B := B) hDenseUniv hDenseB

theorem interior_closure_prod_eq_univ_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y] {A : Set X} {B : Set Y} :
    interior (closure (A ×ˢ B)) = (Set.univ : Set (X × Y)) ↔
      (interior (closure A) = (Set.univ : Set X)) ∧
        (interior (closure B) = (Set.univ : Set Y)) := by
  -- A convenient equality relating the two sides.
  have hProd :
      interior (closure (A ×ˢ B)) =
        interior (closure A) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  constructor
  · intro hUniv
    -- First, show `interior (closure A) = univ`.
    have hA_sub : (Set.univ : Set X) ⊆ interior (closure A) := by
      intro x _
      classical
      let y : Y := Classical.arbitrary Y
      have hxy_in :
          ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) := by
        -- This follows from `hUniv`.
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [hUniv] using this
      have hxy_prod :
          ((x, y) : X × Y) ∈
            interior (closure A) ×ˢ interior (closure B) := by
        simpa [hProd] using hxy_in
      exact (Set.mem_prod.1 hxy_prod).1
    have hIntA_eq :
        interior (closure A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · exact hA_sub
    -- Next, show `interior (closure B) = univ`.
    have hB_sub : (Set.univ : Set Y) ⊆ interior (closure B) := by
      intro y _
      classical
      let x : X := Classical.arbitrary X
      have hxy_in :
          ((x, y) : X × Y) ∈ interior (closure (A ×ˢ B)) := by
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [hUniv] using this
      have hxy_prod :
          ((x, y) : X × Y) ∈
            interior (closure A) ×ˢ interior (closure B) := by
        simpa [hProd] using hxy_in
      exact (Set.mem_prod.1 hxy_prod).2
    have hIntB_eq :
        interior (closure B) = (Set.univ : Set Y) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · exact hB_sub
    exact ⟨hIntA_eq, hIntB_eq⟩
  · rintro ⟨hA, hB⟩
    -- Use `hProd` together with the two equalities.
    calc
      interior (closure (A ×ˢ B))
          = interior (closure A) ×ˢ interior (closure B) := hProd
      _ = (Set.univ : Set X) ×ˢ (Set.univ : Set Y) := by
          simpa [hA, hB]
      _ = (Set.univ : Set (X × Y)) := by
          simpa using
            (Set.univ_prod_univ : ((Set.univ : Set X) ×ˢ (Set.univ : Set Y)) =
              (Set.univ : Set (X × Y)))

theorem closure_prod_eq_univ_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [Nonempty Y]
    {A : Set X} {B : Set Y} :
    closure (A ×ˢ B) = (Set.univ : Set (X × Y)) ↔
      (closure (A : Set X) = (Set.univ : Set X)) ∧
        (closure (B : Set Y) = (Set.univ : Set Y)) := by
  classical
  -- Express the closure of a product as a product of closures.
  have hProd :
      closure (A ×ˢ B) =
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
    simpa using closure_prod_eq (s := A) (t := B)
  constructor
  · intro hUniv
    -- From `hUniv`, deduce that the product of closures is `univ`.
    have hProdUniv :
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) =
          (Set.univ : Set (X × Y)) := by
      simpa [hProd] using hUniv
    -- Prove `closure A = univ`.
    have hA_univ : closure (A : Set X) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · intro x _
        -- Choose an arbitrary `y : Y`.
        let y : Y := Classical.arbitrary Y
        have : ((x, y) : X × Y) ∈
            (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
          have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
            trivial
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).1
    -- Prove `closure B = univ`.
    have hB_univ : closure (B : Set Y) = (Set.univ : Set Y) := by
      apply Set.Subset.antisymm
      · intro _ _; trivial
      · intro y _
        -- Choose an arbitrary `x : X`.
        let x : X := Classical.arbitrary X
        have : ((x, y) : X × Y) ∈
            (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
          have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
            trivial
          simpa [hProdUniv] using this
        exact (Set.mem_prod.1 this).2
    exact ⟨hA_univ, hB_univ⟩
  · rintro ⟨hA_univ, hB_univ⟩
    -- The product of `univ` sets is `univ`.
    have hProdEqUniv :
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) =
          (Set.univ : Set (X × Y)) := by
      simpa [hA_univ, hB_univ, Set.univ_prod_univ]
    -- Rewrite back to the closure of the product.
    simpa [hProd] using hProdEqUniv

theorem closure_subset_closure_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ interior (closure B)) :
    closure A ⊆ closure (interior (closure B)) := by
  exact closure_mono hAB



theorem P1_and_dense_implies_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Dense (interior A) := by
  intro hP1 hDenseA
  have hEquiv := (Topology.P1_dense_iff_denseInterior (X := X) (A := A)) hP1
  exact hEquiv.mp hDenseA

theorem isOpen_closure_interior_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : IsOpen (closure (interior A)) := by
  -- By density, the closure of `interior A` is the whole space.
  have h_closure_eq : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Since `univ` is open, the required set is open as well.
  simpa [h_closure_eq] using isOpen_univ

theorem closure_prod_eq_closure_interior_prod_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    closure (A ×ˢ B) = closure (interior A) ×ˢ closure (interior B) := by
  -- Express `closure A` and `closure B` via the `P1` property.
  have hA_cl : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hA
  have hB_cl : closure (B : Set Y) = closure (interior B) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := Y) (A := B)).1 hB
  -- Rewrite the closure of the product using these equalities.
  calc
    closure (A ×ˢ B) =
        closure (A : Set X) ×ˢ closure (B : Set Y) := by
          simpa using closure_prod_eq (s := A) (t := B)
    _ = closure (interior A) ×ˢ closure (interior B) := by
          simpa [hA_cl, hB_cl]

theorem interior_closure_interior_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior (closure (interior (A ×ˢ B))) =
      interior (closure (interior A)) ×ˢ
        interior (closure (interior B)) := by
  -- First, rewrite the closure of the interior of the product.
  have h₁ :
      closure (interior (A ×ˢ B)) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa using
      (closure_interior_prod (X := X) (Y := Y) (A := A) (B := B))
  -- Next, identify the interior of a product of sets.
  have h₂ :
      interior ((closure (interior A)) ×ˢ (closure (interior B))) =
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) := by
    simpa using
      (interior_prod_eq
        (s := closure (interior A)) (t := closure (interior B)))
  -- Combine the two equalities.
  simpa [h₁, h₂]

theorem interior_inter_left_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) : interior (A ∩ B) = A ∩ interior B := by
  calc
    interior (A ∩ B) = interior A ∩ interior B := by
      simpa using interior_inter
    _ = A ∩ interior B := by
      simpa [hA.interior_eq]

theorem denseInterior_implies_P3_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure (interior A)) := by
  intro hDense
  -- `closure (interior A)` is open, thanks to the density of `interior A`.
  have hOpen : IsOpen (closure (interior A)) :=
    isOpen_closure_interior_of_denseInterior (X := X) (A := A) hDense
  -- Open sets satisfy `P3`.
  exact Topology.isOpen_implies_P3
    (X := X) (A := closure (interior A)) hOpen

theorem P3_prod_closure_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : IsOpen (closure A)) (hB : IsOpen (closure B)) :
    Topology.P3 (closure A ×ˢ closure B) := by
  -- Obtain `P3` for each factor from the openness of its closure
  have hP3A : Topology.P3 (closure A) := by
    have hEquiv := (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A))
    exact hEquiv.mpr hA
  have hP3B : Topology.P3 (closure B) := by
    have hEquiv := (Topology.P3_closure_iff_isOpen_closure (X := Y) (A := B))
    exact hEquiv.mpr hB
  -- Combine the two `P3` properties using the product rule
  simpa using
    (Topology.P3_prod
      (X := X) (Y := Y)
      (A := closure A) (B := closure B) hP3A hP3B)

theorem interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior A ⊆ interior (closure B) := by
  intro x hxA
  -- First enlarge from `A` to `B` using monotonicity of `interior`.
  have hxB : x ∈ interior B := (interior_mono hAB) hxA
  -- Since `B ⊆ closure B`, enlarge once more.
  have hBC : interior B ⊆ interior (closure B) :=
    interior_mono (subset_closure : (B : Set X) ⊆ closure B)
  exact hBC hxB

theorem closure_prod_nonempty_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    (closure (A ×ˢ B)).Nonempty ↔
      ((closure (A : Set X)).Nonempty ∧ (closure (B : Set Y)).Nonempty) := by
  -- Express the closure of the product as a product of closures.
  have hEq :
      closure (A ×ˢ B) =
        (closure (A : Set X)) ×ˢ (closure (B : Set Y)) := by
    simpa using closure_prod_eq (s := A) (t := B)
  constructor
  · -- `→` direction
    intro hProd
    rcases hProd with ⟨p, hp⟩
    -- Transport the membership through `hEq`.
    have hp' : (p : X × Y) ∈ closure A ×ˢ closure B := by
      simpa [hEq] using hp
    rcases hp' with ⟨hpA, hpB⟩
    exact ⟨⟨p.1, hpA⟩, ⟨p.2, hpB⟩⟩
  · -- `←` direction
    rintro ⟨hA, hB⟩
    rcases hA with ⟨x, hx⟩
    rcases hB with ⟨y, hy⟩
    -- Build a point in the product of closures.
    have hMem : ((x, y) : X × Y) ∈ closure A ×ˢ closure B := by
      exact And.intro hx hy
    -- Translate the membership back via `hEq`.
    have hProdMem : ((x, y) : X × Y) ∈ closure (A ×ˢ B) := by
      simpa [hEq] using hMem
    exact ⟨(x, y), hProdMem⟩

theorem P1_prod_closure_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : IsOpen (closure A)) (hB : IsOpen (closure B)) :
    Topology.P1 (closure A ×ˢ closure B) := by
  -- The product of two open sets is open.
  have hOpen : IsOpen (closure A ×ˢ closure B) := hA.prod hB
  -- Open sets satisfy `P1`.
  exact
    Topology.isOpen_implies_P1
      (X := X × Y)
      (A := closure A ×ˢ closure B)
      hOpen

theorem denseInterior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ interior (closure (interior A)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact
      interior_closure_interior_eq_univ_of_dense
        (X := X) (A := A) hDense
  · intro hIntEq
    -- From `interior (closure (interior A)) = univ` we deduce
    -- `closure (interior A) = univ`, hence density.
    have h_closure_eq : closure (interior A : Set X) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro x _
        trivial
      · have h_sub : (Set.univ : Set X) ⊆ closure (interior A) := by
          have : (Set.univ : Set X) = interior (closure (interior A)) := by
            simpa [hIntEq]
          simpa [this] using interior_subset
        exact h_sub
    exact
      (dense_iff_closure_eq (s := interior A)).2 h_closure_eq

theorem denseInterior_implies_P2_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P2 (closure (interior A)) := by
  -- From the density of `interior A`, we know that its closure is open.
  have hOpen : IsOpen (closure (interior A)) :=
    isOpen_closure_interior_of_denseInterior (X := X) (A := A) hDense
  -- For a closed set, `P2` is equivalent to openness.
  exact
    (Topology.P2_closure_interior_iff_isOpen_closure_interior
        (X := X) (A := A)).2 hOpen

theorem closure_union_subset_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `closure A` is contained in the closure of the union.
      have h_subset : closure A ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
        exact closure_mono this
      exact h_subset hA
  | inr hB =>
      -- `closure B` is contained in the closure of the union.
      have h_subset : closure B ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
        exact closure_mono this
      exact h_subset hB

theorem dense_of_P3_and_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      interior (closure A) = (Set.univ : Set X) →
        Dense A := by
  intro _hP3 hIntEq
  -- `interior (closure A)` is contained in `closure A`
  have h_subset : interior (closure A) ⊆ closure A := interior_subset
  -- Hence `closure A` contains all points of the space
  have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
    simpa [hIntEq] using h_subset
  -- Combine with the trivial reverse inclusion to get equality
  have h_closure_eq : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; exact Set.mem_univ x
    · exact h_univ_subset
  -- Conclude density from the characterisation via closure
  exact (dense_iff_closure_eq (s := A)).2 h_closure_eq

theorem closure_interior_four_iter_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- Define the iteration `F` := closure ∘ interior.
  let F : Set X → Set X := fun S ↦ closure (interior S)
  -- Idempotence: `F (F S) = F S`.
  have h_id : ∀ S : Set X, F (F S) = F S := by
    intro S
    simpa [F] using
      (closure_interior_closure_interior_closure_eq (X := X) (A := S))
  -- Apply idempotence successively to collapse four iterations to one.
  have h1 : F (F (F (F A))) = F (F (F A)) := by
    simpa [F] using h_id (F (F A))
  have h2 : F (F (F A)) = F (F A) := by
    simpa [F] using h_id (F A)
  have h3 : F (F A) = F A := by
    simpa [F] using h_id A
  have h_final : F (F (F (F A))) = F A := by
    calc
      F (F (F (F A))) = F (F (F A)) := h1
      _ = F (F A) := h2
      _ = F A := h3
  -- Unfold `F` to obtain the desired equality.
  simpa [F] using h_final

theorem dense_closed_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) (hClosed : IsClosed A) :
    A = (Set.univ : Set X) := by
  -- The density of `A` gives `closure A = univ`.
  have hClosure : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Since `A` is closed, `closure A = A`.
  have hClosedEq : closure A = A := hClosed.closure_eq
  -- Combine the two equalities to obtain the result.
  simpa [hClosedEq] using hClosure

theorem dense_union_of_dense_left_and_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense A → Dense B → Dense (A ∪ B) := by
  intro hA hB
  have hA_closure : closure A = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  have hB_closure : closure B = (Set.univ : Set X) := by
    simpa using hB.closure_eq
  -- Any point of the space belongs to `closure A`, hence to `closure (A ∪ B)`.
  have h_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
    have h_incl : closure A ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
    simpa [hA_closure] using h_incl
  -- Consequently, `closure (A ∪ B)` is the whole space.
  have h_closure_union : closure (A ∪ B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact h_subset
  -- Translate the closure equality into density.
  exact (dense_iff_closure_eq (s := A ∪ B)).2 h_closure_union

theorem denseInterior_implies_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior A) → closure A = (Set.univ : Set X) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have h_closureInt : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Since `interior A ⊆ A`, we have `closure (interior A) ⊆ closure A`.
  have h_subset : (Set.univ : Set X) ⊆ closure A := by
    have : (closure (interior A : Set X)) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [h_closureInt] using this
  -- Combine the two inclusions to obtain the desired equality.
  apply Set.Subset.antisymm
  · intro _ _; trivial
  · exact h_subset

theorem P3_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A ⊆ closure (interior (closure A)) := by
  intro hP3
  intro x hxA
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  have h_sub : interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  exact h_sub hx_int

theorem denseInterior_implies_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense A := by
  intro hDenseInt
  -- From the density of `interior A` we know `closure A = univ`.
  have h_closure_eq : closure A = (Set.univ : Set X) :=
    denseInterior_implies_closure_eq_univ (X := X) (A := A) hDenseInt
  -- Translate the closure equality into density.
  exact (dense_iff_closure_eq (s := A)).2 h_closure_eq

theorem interior_closure_prod_of_dense_left
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hDense : Dense A) :
    interior (closure (A ×ˢ B)) =
      (Set.univ : Set X) ×ˢ interior (closure B) := by
  -- Express the interior of the closure of the product.
  have hProd :
      interior (closure (A ×ˢ B)) =
        interior (closure (A : Set X)) ×ˢ interior (closure B) :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  -- Since `A` is dense, its closure is the whole space.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Hence the interior of this closure is also the whole space.
  have hIntClosureA : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    have : interior (closure (A : Set X)) = interior ((Set.univ : Set X)) := by
      simpa [hClosureA]
    simpa [interior_univ] using this
  -- Substitute and simplify.
  simpa [hIntClosureA] using hProd

theorem P3_iff_P2_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P3 A ↔ Topology.P2 A := by
  -- From the density of `interior A` we immediately obtain `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.denseInterior_implies_P1 (X := X) (A := A) hDense
  constructor
  · intro hP3
    exact Topology.P3_and_P1_implies_P2 (X := X) (A := A) hP3 hP1
  · intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2

theorem denseInterior_left_implies_P2_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense (interior A) → Topology.P2 (A ∪ B) := by
  intro hDense
  dsimp [Topology.P2]
  intro x _hx
  -- `closure (interior A)` is the whole space.
  have h_closure_intA : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A ⊆ interior (A ∪ B)`
  have h_int_subset : interior A ⊆ interior (A ∪ B) := by
    have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
    exact interior_mono this
  -- hence `closure (interior A) ⊆ closure (interior (A ∪ B))`
  have h_closure_subset :
      (closure (interior A : Set X)) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_int_subset
  -- together with the previous equality we get `closure (interior (A ∪ B)) = univ`
  have h_closure_univ :
      closure (interior (A ∪ B) : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; exact Set.mem_univ y
    · simpa [h_closure_intA] using h_closure_subset
  -- therefore its interior is also the whole space
  have h_interior_univ :
      interior (closure (interior (A ∪ B))) = (Set.univ : Set X) := by
    simpa [h_closure_univ, interior_univ]
  -- conclude the desired membership
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior_univ] using this

theorem interior_inter_right_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) : interior (A ∩ B) = interior A ∩ B := by
  calc
    interior (A ∩ B) = interior A ∩ interior B := by
      simpa using interior_inter (A := A) (B := B)
    _ = interior A ∩ B := by
      simpa [hB.interior_eq]

theorem interior_closure_union_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hClosure
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- If `A` is empty, its closure is also empty, contradicting `hClosure`.
      have hA_eq : (A : Set X) = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hClosure_eq : closure (A : Set X) = (∅ : Set X) := by
        simpa [hA_eq, closure_empty]
      have hEmptyNonempty : (∅ : Set X).Nonempty := by
        simpa [hClosure_eq] using hClosure
      rcases hEmptyNonempty with ⟨x, hx⟩
      cases hx
  · intro hA
    rcases hA with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩

theorem closure_interiors_union_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆ closure (interior (A ∪ B)) := by
  -- `interior A ∪ interior B` is contained in `interior (A ∪ B)`
  have h_subset : interior A ∪ interior B ⊆ interior (A ∪ B) :=
    interior_union (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusion
  exact closure_mono h_subset

theorem closureInterior_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A) : Set X).Nonempty ↔ (interior A).Nonempty := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    -- If `interior A` were empty, its closure would also be empty,
    -- contradicting the existence of `x`.
    have : (interior A).Nonempty := by
      by_contra hIntEmpty
      have hIntEq : interior A = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hIntEmpty
      have : x ∈ (∅ : Set X) := by
        simpa [hIntEq, closure_empty] using hx
      exact this.elim
    exact this
  · rintro ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩

theorem interior_prod_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ×ˢ B) = A ×ˢ B := by
  have h := interior_prod_eq (s := A) (t := B)
  simpa [hA.interior_eq, hB.interior_eq] using h

theorem closure_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  -- The interior of an open set is itself.
  have h : interior (interior A) = interior A := by
    simpa using (isOpen_interior (A := A)).interior_eq
  simpa [h]

theorem denseInterior_left_and_P2_right_implies_P2_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Dense (interior A) → Topology.P2 B → Topology.P2 (A ×ˢ B) := by
  intro hDenseInt hP2B
  dsimp [Topology.P2] at hP2B ⊢
  intro p hp
  -- Coordinates of the point `p`
  have hxA : p.1 ∈ A := hp.1
  have hyB : p.2 ∈ B := hp.2
  -- Thanks to the density of `interior A`, its closure's interior is the whole space
  have hIntA_univ :
      interior (closure (interior A : Set X)) = (Set.univ : Set X) :=
    interior_closure_interior_eq_univ_of_dense (X := X) (A := A) hDenseInt
  -- Hence `p.1` lies in `interior (closure (interior A))`
  have hx_int :
      p.1 ∈ interior (closure (interior A)) := by
    have : p.1 ∈ (Set.univ : Set X) := by
      trivial
    simpa [hIntA_univ] using this
  -- Apply the `P2` property of `B` to the second coordinate
  have hy_int :
      p.2 ∈ interior (closure (interior B)) := hP2B hyB
  -- Combine the two interior memberships
  have h_mem_prod :
      (p : X × Y) ∈
        interior (closure (interior A)) ×ˢ
          interior (closure (interior B)) :=
    And.intro hx_int hy_int
  -- Identify `interior (closure (interior (A ×ˢ B)))`
  have h_eq :=
    interior_closure_interior_prod (X := X) (Y := Y) (A := A) (B := B)
  -- Conclude the desired membership
  simpa [h_eq] using h_mem_prod

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior (closure A)) = interior (closure A) := by
  simpa using (isOpen_interior (A := closure A)).interior_eq

theorem interior_union_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  simpa using hOpen.interior_eq

theorem dense_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Dense (closure A) := by
  intro hDense
  -- The closure of a dense set is the whole space,
  -- hence its closure (taken once more) is also the whole space.
  have h_closure :
      closure (closure A : Set X) = (Set.univ : Set X) := by
    simpa [hDense.closure_eq, closure_univ, closure_closure]
  -- Translate this equality into the desired density statement.
  exact (dense_iff_closure_eq (s := closure A)).2 h_closure

theorem dense_of_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) → Dense A := by
  intro hIntEq
  -- First, show that `closure A = univ`.
  have hClosureEq : closure A = (Set.univ : Set X) := by
    -- `interior (closure A)` is contained in `closure A`.
    have hIntSub : interior (closure A) ⊆ closure A := interior_subset
    -- Hence `univ ⊆ closure A`.
    have hUnivSub : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      have : x ∈ interior (closure A) := by
        simpa [hIntEq]
      exact hIntSub this
    -- Combine the trivial inclusion `closure A ⊆ univ` with the one above.
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · exact hUnivSub
  -- Translate the closure equality into density.
  exact
    ((dense_iff_closure_eq (s := A)).2 hClosureEq)

theorem interior_eq_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = A) : Topology.P1 A := by
  -- From `interior A = A` we deduce that `A` is open.
  have hOpen : IsOpen A := by
    simpa [hInt] using (isOpen_interior : IsOpen (interior A))
  -- Open sets satisfy `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem dense_prod_left_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) :
    Dense (A ×ˢ B) → Dense A := by
  intro hDense
  -- `closure (A ×ˢ B)` is the whole space.
  have h_closure_prod :
      (closure (A ×ˢ B : Set (X × Y))) = (Set.univ : Set (X × Y)) := by
    simpa using hDense.closure_eq
  -- We show `closure A = univ`, which is equivalent to `Dense A`.
  have h_closureA_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    -- First, the easy inclusion `closure A ⊆ univ`.
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · -- For the reverse inclusion, fix an arbitrary `x : X`.
      intro x _
      -- Pick some `y ∈ B`.
      rcases hBne with ⟨y, hyB⟩
      -- The point `(x, y)` lies in `univ`, hence in `closure (A ×ˢ B)`.
      have h_mem_closure_prod :
          ((x, y) : X × Y) ∈ closure (A ×ˢ B) := by
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [h_closure_prod] using this
      -- Rewrite `closure (A ×ˢ B)` as a product of closures.
      have h_prod_eq :
          (closure (A ×ˢ B) : Set (X × Y)) =
            closure (A : Set X) ×ˢ closure (B : Set Y) := by
        simpa using closure_prod_eq (s := A) (t := B)
      -- Extract the first coordinate.
      have : ((x, y) : X × Y) ∈ closure A ×ˢ closure B := by
        simpa [h_prod_eq] using h_mem_closure_prod
      exact (Set.mem_prod.1 this).1
  -- Conclude density from the characterisation via closures.
  exact (dense_iff_closure_eq (s := A)).2 h_closureA_univ

theorem P3_prod_left_iff_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) (hP3B : Topology.P3 B) :
    Topology.P3 (A ×ˢ B) ↔ Topology.P3 A := by
  constructor
  · intro hProd
    exact
      (Topology.P3_prod_left_of_nonempty
        (X := X) (Y := Y) (A := A) (B := B) hBne) hProd
  · intro hP3A
    exact
      Topology.P3_prod (X := X) (Y := Y) (A := A) (B := B) hP3A hP3B

theorem dense_prod_right_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) :
    Dense (A ×ˢ B) → Dense B := by
  intro hDenseProd
  -- `closure (A ×ˢ B)` is the whole space.
  have h_closure_prod :
      closure (A ×ˢ B : Set (X × Y)) = (Set.univ : Set (X × Y)) := by
    simpa using hDenseProd.closure_eq
  -- Express this closure as a product of closures.
  have h_prod_closure :
      closure (A ×ˢ B : Set (X × Y)) =
        (closure (A : Set X)) ×ˢ closure (B : Set Y) := by
    simpa using closure_prod_eq (s := A) (t := B)
  -- We prove `closure B = univ`, which implies `Dense B`.
  have h_closureB_univ : closure (B : Set Y) = (Set.univ : Set Y) := by
    -- First, the trivial inclusion.
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · intro y _
      -- Choose an arbitrary `x ∈ A`.
      rcases hAne with ⟨x, hxA⟩
      -- The point `(x, y)` lies in `univ`, hence in `closure (A ×ˢ B)`.
      have h_mem_closure_prod :
          ((x, y) : X × Y) ∈ closure (A ×ˢ B) := by
        have : ((x, y) : X × Y) ∈ (Set.univ : Set (X × Y)) := by
          trivial
        simpa [h_closure_prod] using this
      -- Transport this membership through `h_prod_closure`.
      have h_mem_prod_closures :
          ((x, y) : X × Y) ∈
            (closure (A : Set X)) ×ˢ closure (B : Set Y) := by
        simpa [h_prod_closure] using h_mem_closure_prod
      -- Extract the `Y`-component.
      exact (Set.mem_prod.1 h_mem_prod_closures).2
  -- Conclude density via the characterisation using closures.
  exact (dense_iff_closure_eq (s := B)).2 h_closureB_univ

theorem interior_eq_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A → Topology.P2 A := by
  intro hInt
  -- From `interior A = A` we deduce that `A` is open.
  have hOpen : IsOpen A := by
    have hOpenInt : IsOpen (interior A) := isOpen_interior
    simpa [hInt] using hOpenInt
  -- Open sets satisfy the `P2` property.
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem interior_closure_nonempty_iff_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A →
      ((interior (closure A)).Nonempty ↔ A.Nonempty) := by
  intro hP3
  constructor
  · intro hInt
    -- From the non‐emptiness of `interior (closure A)` we deduce that `closure A`
    -- is nonempty, and hence (by a standard lemma) so is `A`.
    have hClos : (closure (A : Set X)).Nonempty := by
      rcases hInt with ⟨x, hx⟩
      exact ⟨x, (interior_subset : interior (closure A) ⊆ closure A) hx⟩
    exact (closure_nonempty_iff (X := X) (A := A)).1 hClos
  · intro hA
    -- Thanks to `P3`, any point of `A` lies in `interior (closure A)`.
    rcases hA with ⟨x, hx⟩
    exact ⟨x, hP3 hx⟩

theorem dense_closure_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure A) ↔ Dense A := by
  constructor
  · intro hDenseClosure
    -- From the density of `closure A`, we get `closure (closure A) = univ`.
    have h₁ : closure (closure A : Set X) = (Set.univ : Set X) := by
      simpa using hDenseClosure.closure_eq
    -- Using `closure_closure`, deduce `closure A = univ`, hence `Dense A`.
    have h₂ : closure (A : Set X) = (Set.univ : Set X) := by
      simpa [closure_closure] using h₁
    exact (dense_iff_closure_eq (s := A)).2 h₂
  · intro hDenseA
    -- The closure of a dense set is dense.
    exact dense_closure_of_dense (X := X) (A := A) hDenseA

theorem interior_closure_inter_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∩ closure A = interior (closure A) := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro hx
    exact And.intro hx (interior_subset hx)

theorem interior_nonempty_iff_nonempty_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → ((interior A).Nonempty ↔ A.Nonempty) := by
  intro hP1
  constructor
  · intro hInt
    rcases hInt with ⟨x, hx⟩
    exact ⟨x, interior_subset hx⟩
  · intro hA
    exact
      Topology.interior_nonempty_of_P1 (X := X) (A := A) hP1 hA

theorem interior_nonempty_iff_nonempty_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → ((interior A).Nonempty ↔ A.Nonempty) := by
  intro hP2
  constructor
  · intro hInt
    rcases hInt with ⟨x, hx⟩
    exact ⟨x, interior_subset hx⟩
  · intro hA
    exact
      Topology.interior_nonempty_of_P2 (X := X) (A := A) hP2 hA

theorem dense_iff_closure_mem_nhds {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ ∀ x : X, closure A ∈ 𝓝 x := by
  constructor
  · intro hDense x
    -- Since `A` is dense, its closure is the whole space.
    have h_cl : (closure A : Set X) = Set.univ := hDense.closure_eq
    -- `univ` is a neighbourhood of every point.
    have h_nhds_univ : (Set.univ : Set X) ∈ 𝓝 x := by
      exact (isOpen_univ.mem_nhds trivial)
    simpa [h_cl] using h_nhds_univ
  · intro h
    -- Show that `closure A = univ`, whence density of `A`.
    have h_sub : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      have h_nhds : closure A ∈ 𝓝 x := h x
      have h_int : x ∈ interior (closure A) :=
        (mem_interior_iff_mem_nhds).2 h_nhds
      exact interior_subset h_int
    have h_closure_eq : (closure A : Set X) = Set.univ := by
      apply Set.Subset.antisymm
      · intro x _; trivial
      · exact h_sub
    exact ((dense_iff_closure_eq (s := A)).2 h_closure_eq)

theorem interior_eq_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = A → Topology.P3 A := by
  intro hIntEq
  -- From `interior A = A` we deduce that `A` is open.
  have hOpen : IsOpen A := by
    simpa [hIntEq] using (isOpen_interior : IsOpen (interior A))
  -- Open sets satisfy `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem interior_closure_prod_of_dense_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hDense : Dense B) :
    interior (closure (A ×ˢ B)) =
      interior (closure A) ×ˢ (Set.univ : Set Y) := by
  -- Start from the general description of the left‐hand side.
  have hProd :=
    interior_closure_prod (X := X) (Y := Y) (A := A) (B := B)
  -- A dense set has the whole space as its closure.
  have hClosureB : closure (B : Set Y) = (Set.univ : Set Y) := by
    simpa using hDense.closure_eq
  -- Therefore its interior is also the whole space.
  have hIntClosureB : interior (closure (B : Set Y)) = (Set.univ : Set Y) := by
    have : interior (closure (B : Set Y)) = interior ((Set.univ : Set Y)) := by
      simpa [hClosureB]
    simpa [interior_univ] using this
  -- Substitute into the original equality.
  simpa [hIntClosureB] using hProd

theorem denseInterior_prod_of_denseInterior_left_and_denseInterior_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : Dense (interior A)) (hB : Dense (interior B)) :
    Dense (interior (A ×ˢ B)) := by
  -- Characterize density through closure.
  have hA_closure : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  have hB_closure : closure (interior B : Set Y) = (Set.univ : Set Y) := by
    simpa using hB.closure_eq
  -- Rewrite the closure of the interior of the product.
  have h_int_prod :
      interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  have h_closure_prod :
      closure (interior (A ×ˢ B) : Set (X × Y)) =
        closure (interior A) ×ˢ closure (interior B) := by
    simpa [h_int_prod] using
      (closure_prod_eq (s := interior A) (t := interior B))
  -- Combine the above to obtain that the closure is the whole space.
  have h_closure_eq_univ :
      closure (interior (A ×ˢ B) : Set (X × Y)) =
        (Set.univ : Set (X × Y)) := by
    simpa [hA_closure, hB_closure, Set.univ_prod_univ] using h_closure_prod
  -- Conclude density from the closure characterization.
  exact (dense_iff_closure_eq).2 h_closure_eq_univ

theorem denseInterior_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hAne : (interior A).Nonempty) (hBne : (interior B).Nonempty) :
    Dense (interior (A ×ˢ B)) ↔
      (Dense (interior A) ∧ Dense (interior B)) := by
  -- Identify the interior of a product.
  have hInt : interior (A ×ˢ B) = (interior A) ×ˢ (interior B) := by
    simpa using interior_prod_eq (s := A) (t := B)
  -- Rewrite the goal with this identification.
  have hRew :
      Dense (interior (A ×ˢ B)) ↔
        Dense ((interior A) ×ˢ (interior B)) := by
    simpa [hInt]
  -- Apply the density criterion for products to the interiors.
  have hProd :=
    (dense_prod_iff
        (X := X) (Y := Y)
        (A := interior A) (B := interior B)
        (hAne := hAne) (hBne := hBne))
  -- Combine the two equivalences.
  exact hRew.trans hProd

theorem P1_and_denseInterior_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense (interior A) → Topology.P2 A := by
  intro _ hDenseInt
  exact
    Topology.denseInterior_implies_P2 (X := X) (A := A) hDenseInt

theorem dense_of_P1_and_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A)
    (hInt : interior (closure (interior A)) = (Set.univ : Set X)) :
    Dense A := by
  -- First, show that `closure (interior A)` is the whole space.
  have h_closure_int : closure (interior A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    ·
      have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      simpa [hInt] using h_subset
  -- From `P1`, deduce `closure A = closure (interior A)`.
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Hence `closure A = univ`.
  have h_closureA_univ : closure A = (Set.univ : Set X) := by
    simpa [h_closure_int] using h_closure_eq
  -- Translate this equality into density of `A`.
  exact (dense_iff_closure_eq (s := A)).2 h_closureA_univ

theorem P2_union_of_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2A : Topology.P2 A) (hBsubset : B ⊆ interior (closure (interior A))) :
    Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hP2A ⊢
  intro x hx
  -- First locate `x` inside `interior (closure (interior A))`.
  have hxIntA : x ∈ interior (closure (interior A)) := by
    cases hx with
    | inl hxA => exact hP2A hxA
    | inr hxB => exact hBsubset hxB
  -- Monotonicity of `interior` and `closure` gives the required inclusion.
  have hMono :
      interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) := by
    -- Step 1: `interior A ⊆ interior (A ∪ B)`.
    have hIntSub : interior A ⊆ interior (A ∪ B) := by
      have hSub : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
      exact interior_mono hSub
    -- Step 2: take closures.
    have hClosSub :
        closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono hIntSub
    -- Step 3: take interiors once more.
    exact interior_mono hClosSub
  exact hMono hxIntA

theorem isOpen_closure_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure A) := by
  intro hDense
  have hClosure : (closure A : Set X) = (Set.univ : Set X) :=
    denseInterior_implies_closure_eq_univ (X := X) (A := A) hDense
  simpa [hClosure] using isOpen_univ

theorem closureInterior_eq_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (A : Set X) → Topology.P1 A := by
  intro hEq
  dsimp [Topology.P1]
  intro x hx
  simpa [hEq] using hx

theorem P3_closure_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P3 (closure A ×ˢ closure B) ↔
      (Topology.P3 (closure A) ∧ Topology.P3 (closure B)) := by
  -- Non‐emptiness of the closures follows from the non‐emptiness of the sets.
  have hAneClosure : (closure (A : Set X)).Nonempty := by
    rcases hAne with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩
  have hBneClosure : (closure (B : Set Y)).Nonempty := by
    rcases hBne with ⟨y, hy⟩
    exact ⟨y, subset_closure hy⟩
  -- Apply the existing equivalence for products.
  simpa using
    (Topology.P3_prod_iff
        (X := X) (Y := Y)
        (A := closure A) (B := closure B)
        hAneClosure hBneClosure)

theorem P1_prod_left_iff_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) (hP1B : Topology.P1 B) :
    Topology.P1 (A ×ˢ B) ↔ Topology.P1 A := by
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_left_of_nonempty
        (X := X) (Y := Y) (A := A) (B := B) hBne) hProd
  · intro hP1A
    exact
      Topology.P1_prod
        (X := X) (Y := Y) (A := A) (B := B) hP1A hP1B

theorem dense_prod_left_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hDenseB : Dense B) :
    Dense (A ×ˢ B) ↔ Dense A := by
  -- Start from the general equivalence for products of arbitrary sets.
  have hProd :=
    (dense_prod_iff
        (X := X) (Y := Y) (A := A) (B := B) hAne hBne)
  -- Under the extra hypothesis `Dense B`, the right‐hand side simplifies.
  have hAux : (Dense A ∧ Dense B) ↔ Dense A := by
    constructor
    · intro h; exact h.1
    · intro hA; exact And.intro hA hDenseB
  exact hProd.trans hAux

theorem dense_left_implies_dense_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense A → Dense (A ∪ B) := by
  intro hDenseA
  -- `A` is dense, so its closure is the whole space.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hDenseA.closure_eq
  -- The inclusion `A ⊆ A ∪ B` yields an inclusion of closures.
  have hSubset : closure (A : Set X) ⊆ closure (A ∪ B) :=
    closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Hence `closure (A ∪ B)` contains every point of the space.
  have hUnivSubset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
    simpa [hClosureA] using hSubset
  -- Combine the inclusions to obtain the equality of sets.
  have hClosureUnion : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact hUnivSubset
  -- Translate the closure equality into the desired density statement.
  exact (dense_iff_closure_eq (s := A ∪ B)).2 hClosureUnion

theorem interior_prod_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    interior A ×ˢ interior B ⊆ interior (A ×ˢ B) := by
  -- We rely on the characterization of the interior of a product.
  have h : interior (A ×ˢ B) = interior A ×ˢ interior B := by
    simpa using interior_prod_eq (s := A) (t := B)
  intro z hz
  -- Transport the membership through the equality `h`.
  simpa [h] using hz

theorem isOpen_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsOpen (closure A) := by
  intro hDense
  have h_eq : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  simpa [h_eq] using isOpen_univ

theorem P2_prod_closure_of_isOpen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : IsOpen (closure A)) (hB : IsOpen (closure B)) :
    Topology.P2 (closure A ×ˢ closure B) := by
  -- Each open closure separately satisfies `P2`.
  have hP2A : Topology.P2 (closure A) :=
    Topology.isOpen_implies_P2 (X := X) (A := closure A) hA
  have hP2B : Topology.P2 (closure B) :=
    Topology.isOpen_implies_P2 (X := Y) (A := closure B) hB
  -- Combine them via the product rule for `P2`.
  simpa using
    (Topology.P2_prod
      (X := X) (Y := Y)
      (A := closure A) (B := closure B) hP2A hP2B)





theorem dense_implies_P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (interior (closure A)) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- `closure A` is the whole space because `A` is dense
  have h_closure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- hence its interior is also the whole space
  have h_int_closure : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
      using (congrArg id h_closure)
  -- rewrite the goal using these equalities
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int_closure, closure_univ, interior_univ] using this

theorem P2_closure_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P2 (closure A ×ˢ closure B) ↔
      (Topology.P2 (closure A) ∧ Topology.P2 (closure B)) := by
  -- Closures of nonempty sets are nonempty.
  have hAneClosure : (closure (A : Set X)).Nonempty := by
    rcases hAne with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩
  have hBneClosure : (closure (B : Set Y)).Nonempty := by
    rcases hBne with ⟨y, hy⟩
    exact ⟨y, subset_closure hy⟩
  -- Apply the existing equivalence for products.
  simpa using
    (Topology.P2_prod_iff
        (X := X) (Y := Y)
        (A := closure A) (B := closure B)
        hAneClosure hBneClosure)

theorem interior_inter_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  -- Start from the general description of the interior of an intersection.
  have h : interior (A ∩ B) = interior A ∩ interior B := by
    simpa using interior_inter (A := A) (B := B)
  -- Use the fact that the interior of an open set is the set itself.
  simpa [hA.interior_eq, hB.interior_eq] using h

theorem P1_closure_prod_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) :
    Topology.P1 (closure A ×ˢ closure B) ↔
      (Topology.P1 (closure A) ∧ Topology.P1 (closure B)) := by
  -- The closures of non-empty sets are themselves non-empty.
  have hAneCl : (closure (A : Set X)).Nonempty := by
    rcases hAne with ⟨a, ha⟩
    exact ⟨a, subset_closure ha⟩
  have hBneCl : (closure (B : Set Y)).Nonempty := by
    rcases hBne with ⟨b, hb⟩
    exact ⟨b, subset_closure hb⟩
  -- Use the existing equivalence for products and transport it to closures.
  constructor
  · intro hProd
    exact
      (Topology.P1_prod_implies_P1_left_and_right
          (X := X) (Y := Y)
          (A := closure A) (B := closure B)
          hProd hAneCl hBneCl)
  · rintro ⟨hPA, hPB⟩
    exact
      Topology.P1_prod
        (X := X) (Y := Y)
        (A := closure A) (B := closure B) hPA hPB

theorem P2_prod_left_iff_of_nonempty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty Y]
    {A : Set X} {B : Set Y} (hBne : B.Nonempty) (hP2B : Topology.P2 B) :
    Topology.P2 (A ×ˢ B) ↔ Topology.P2 A := by
  constructor
  · intro hProd
    exact
      (Topology.P2_prod_left_of_nonempty
          (X := X) (Y := Y) (A := A) (B := B) hBne) hProd
  · intro hP2A
    exact
      Topology.P2_prod (X := X) (Y := Y) (A := A) (B := B) hP2A hP2B

theorem interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have hSub : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact hSub hA
  | inr hB =>
      have hSub : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact hSub hB

theorem dense_right_implies_dense_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Dense B → Dense (A ∪ B) := by
  intro hDenseB
  -- Apply the corresponding lemma with the roles of `A` and `B` swapped,
  -- then rewrite using the commutativity of the union.
  have h : Dense (B ∪ A) :=
    dense_left_implies_dense_union (X := X) (A := B) (B := A) hDenseB
  simpa [Set.union_comm] using h

set_option maxRecDepth 1000

theorem dense_implies_P3_interior_closure_fixed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (interior (closure A)) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : (closure A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Consequently, the interior of this closure is also the whole space.
  have h_int_closure : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- The claim now follows trivially.
  simpa [h_int_closure] using (trivial : x ∈ (Set.univ : Set X))

theorem P2_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ closure (interior A) := by
  intro hP2
  intro x hxA
  -- From `P2`, the point `x` lies in `interior (closure (interior A))`.
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  -- The interior of any set is contained in that set.
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact h_subset hx_int

theorem interior_inter_has_all_P {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∩ interior B) ∧
      Topology.P2 (interior A ∩ interior B) ∧
        Topology.P3 (interior A ∩ interior B) := by
  have hA : IsOpen (interior A) := isOpen_interior
  have hB : IsOpen (interior B) := isOpen_interior
  simpa using
    (Topology.isOpen_inter_has_all_P
      (X := X) (A := interior A) (B := interior B) hA hB)

theorem denseInterior_implies_dense_interior_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (interior (closure (interior A))) := by
  intro hDense
  -- First, identify `interior (closure (interior A))` with `univ`.
  have h_eq :
      interior (closure (interior A)) = (Set.univ : Set X) :=
    interior_closure_interior_eq_univ_of_dense (X := X) (A := A) hDense
  -- The closure of `univ` is `univ`, so the closure of our set is `univ`.
  have h_closure :
      (closure (interior (closure (interior A)) : Set X)) =
        (Set.univ : Set X) := by
    simpa [h_eq, closure_univ]
  -- Conclude density from the characterisation via closures.
  exact
    (dense_iff_closure_eq
        (s := interior (closure (interior A)))).2 h_closure

theorem dense_prod_closure_of_dense_left_and_dense_right
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    Dense A → Dense B → Dense (closure A ×ˢ closure B) := by
  intro hA hB
  -- `A` and `B` are dense, so their closures are the whole space.
  have hA_closure : (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa using hA.closure_eq
  have hB_closure : (closure (B : Set Y)) = (Set.univ : Set Y) := by
    simpa using hB.closure_eq
  -- Compute the closure of the product of these closures.
  have hProd :
      closure ((closure A) ×ˢ (closure B) : Set (X × Y)) =
        (Set.univ : Set (X × Y)) := by
    calc
      closure ((closure A) ×ˢ (closure B) : Set (X × Y))
          = closure (closure A) ×ˢ closure (closure B) := by
            simpa using closure_prod_eq (s := closure A) (t := closure B)
      _ = (closure A) ×ˢ (closure B) := by
            simp [closure_closure]
      _ = (Set.univ : Set X) ×ˢ (Set.univ : Set Y) := by
            simpa [hA_closure, hB_closure]
      _ = (Set.univ : Set (X × Y)) := by
            simpa using Set.univ_prod_univ
  -- Conclude density from the characterisation via closures.
  exact (dense_iff_closure_eq (s := closure A ×ˢ closure B)).2 hProd

theorem interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (interior A : Set X) = interior A := by
  simpa using (isOpen_interior (A := A)).interior_eq

theorem closure_prod_closure_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} :
    closure ((closure A) ×ˢ (closure B) : Set (X × Y)) =
      (closure A) ×ˢ (closure B) := by
  calc
    closure ((closure A) ×ˢ (closure B) : Set (X × Y))
        = closure (closure A) ×ˢ closure (closure B) := by
          simpa using
            (closure_prod_eq (s := closure A) (t := closure B))
    _ = (closure A) ×ˢ (closure B) := by
          simpa [closure_closure]

theorem interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior A))) =
      interior (closure (interior A)) := by
  simpa [interior_idempotent]

theorem dense_prod_right_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hAne : A.Nonempty) (hBne : B.Nonempty) (hDenseA : Dense A) :
    Dense (A ×ˢ B) ↔ Dense B := by
  -- Start with the general equivalence for products.
  have h₁ :=
    (dense_prod_iff
      (X := X) (Y := Y) (A := A) (B := B) hAne hBne)
  -- Under the extra hypothesis `Dense A`, the right‐hand side simplifies.
  have h₂ : (Dense A ∧ Dense B) ↔ Dense B := by
    constructor
    · intro h; exact h.2
    · intro hB; exact And.intro hDenseA hB
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem closure_interior_subset_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : closure (interior A) ⊆ A := by
  -- `interior A` is contained in `A`
  have h_int : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusion
  have h_closure : closure (interior A) ⊆ closure A := closure_mono h_int
  -- Since `A` is closed, its closure is itself
  simpa [hA_closed.closure_eq] using h_closure

theorem P3_inter_interior_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A ∩ interior (closure A)) = A := by
  intro hP3
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    exact ⟨hxA, hxInt⟩

theorem interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `interior (closure A) = univ` implies `univ ⊆ closure A`
    have h₁ : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      -- From `hInt`, we know `x ∈ interior (closure A)`
      have hx : x ∈ interior (closure A) := by
        simpa [hInt] using (Set.mem_univ x)
      -- `interior (closure A)` is contained in `closure A`
      exact interior_subset hx
    -- The reverse inclusion is trivial
    have h₂ : (closure A : Set X) ⊆ (Set.univ : Set X) := by
      intro x _; trivial
    exact Set.Subset.antisymm h₂ h₁
  · intro hClos
    -- If `closure A = univ`, so is its interior
    simpa [hClos, interior_univ]