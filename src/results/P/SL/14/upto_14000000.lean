

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h
  dsimp [P2, P1] at h ⊢
  exact Set.Subset.trans h interior_subset

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro h
  dsimp [P2, P3] at h ⊢
  have h1 : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hsubset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono hsubset
  exact Set.Subset.trans h h1

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  simpa [hA.interior_eq] using hsubset

theorem Topology.isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  exact Topology.P2_implies_P3 (Topology.isOpen_implies_P2 hA)

theorem interior_satisfies_P2 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    interior_maximal (subset_closure : interior A ⊆ closure (interior A))
      isOpen_interior

theorem isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA.interior_eq] using (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.interior_satisfies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  exact Topology.P2_implies_P3 (Topology.interior_satisfies_P2 A)

theorem closure_has_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hA
  dsimp [Topology.P3] at hA
  dsimp [Topology.P1]
  exact closure_mono hA

theorem interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  exact Topology.isOpen_implies_P1 (X := X) (A := interior A) isOpen_interior

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro h
  exact
    ⟨Topology.P2_implies_P1 (X := X) (A := A) h,
     Topology.P2_implies_P3 (X := X) (A := A) h⟩

theorem Topology.empty_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P1, Topology.P2, Topology.P3]
  simp

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  dsimp [Topology.P1] at *
  -- `A` is contained in `closure (interior (A ∪ B))`
  have hA' : (A : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hA_to_closure : (A : Set X) ⊆ closure (interior A) := hA
    have h_closure_mono : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
      have h_int_mono : interior A ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro x hx
          exact Or.inl hx)
      exact closure_mono h_int_mono
    exact Set.Subset.trans hA_to_closure h_closure_mono
  -- `B` is contained in `closure (interior (A ∪ B))`
  have hB' : (B : Set X) ⊆ closure (interior (A ∪ B)) := by
    have hB_to_closure : (B : Set X) ⊆ closure (interior B) := hB
    have h_closure_mono : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
      have h_int_mono : interior B ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro x hx
          exact Or.inr hx)
      exact closure_mono h_int_mono
    exact Set.Subset.trans hB_to_closure h_closure_mono
  -- Hence `A ∪ B` is contained in `closure (interior (A ∪ B))`
  exact Set.union_subset hA' hB'

theorem Topology.P2_iff_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2
  · intro hP3
    dsimp [Topology.P2, Topology.P3] at hP3 ⊢
    simpa [hA.interior_eq] using hP3

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  -- `A` is contained in `interior (closure (A ∪ B))`
  have hA' : (A : Set X) ⊆ interior (closure (A ∪ B)) := by
    have hA_to_int : (A : Set X) ⊆ interior (closure A) := hA
    have h_int_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
      have h_closure_mono : closure A ⊆ closure (A ∪ B) := by
        have h_subset : (A : Set X) ⊆ (A ∪ B) := by
          intro x hx
          exact Or.inl hx
        exact closure_mono h_subset
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hA_to_int h_int_mono
  -- `B` is contained in `interior (closure (A ∪ B))`
  have hB' : (B : Set X) ⊆ interior (closure (A ∪ B)) := by
    have hB_to_int : (B : Set X) ⊆ interior (closure B) := hB
    have h_int_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
      have h_closure_mono : closure B ⊆ closure (A ∪ B) := by
        have h_subset : (B : Set X) ⊆ (A ∪ B) := by
          intro x hx
          exact Or.inr hx
        exact closure_mono h_subset
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hB_to_int h_int_mono
  -- Hence `A ∪ B` is contained in `interior (closure (A ∪ B))`
  exact Set.union_subset hA' hB'

theorem Topology.closure_has_P1_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  -- First, take closures of both sides of `hA`.
  have h1 : (closure A : Set X) ⊆ closure (interior A) := by
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa using this
  -- Next, use the monotonicity of `interior` and `closure` to enlarge the right-hand side.
  have h2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono this
  -- Combining the two inclusions yields the desired result.
  exact Set.Subset.trans h1 h2

theorem Topology.P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  have h_closure : closure A = A := hA_closed.closure_eq
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    have h1 : (A : Set X) ⊆ interior A := by
      simpa [h_closure] using hP3
    have h2 : interior A ⊆ A := interior_subset
    have h_eq : interior A = A := Set.Subset.antisymm h2 h1
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hA_open
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hA_open

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  dsimp [Topology.P2] at hA hB ⊢
  -- First, upgrade the target set for `A`.
  have hA' : (A : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    -- `A` is already inside `interior (closure (interior A))`.
    have hA_to : (A : Set X) ⊆ interior (closure (interior A)) := hA
    -- `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`.
    have h_incl : interior (closure (interior A))
        ⊆ interior (closure (interior (A ∪ B))) := by
      -- Monotonicity of `closure` and `interior`.
      have h_closure_mono :
          closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have h_int_mono : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have h_subset : (A : Set X) ⊆ (A ∪ B) := by
            intro x hx
            exact Or.inl hx
          exact interior_mono h_subset
        exact closure_mono h_int_mono
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hA_to h_incl
  -- Next, upgrade the target set for `B`.
  have hB' : (B : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    have hB_to : (B : Set X) ⊆ interior (closure (interior B)) := hB
    have h_incl : interior (closure (interior B))
        ⊆ interior (closure (interior (A ∪ B))) := by
      have h_closure_mono :
          closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h_int_mono : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have h_subset : (B : Set X) ⊆ (A ∪ B) := by
            intro x hx
            exact Or.inr hx
          exact interior_mono h_subset
        exact closure_mono h_int_mono
      exact interior_mono h_closure_mono
    exact Set.Subset.trans hB_to h_incl
  -- Finally, combine the two inclusions.
  exact Set.union_subset hA' hB'

theorem Topology.closure_has_P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact Topology.closure_has_P1_of_P3 (X := X) (A := A) hP3

theorem Topology.P1_iff_closureInterior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  dsimp [Topology.P1]
  constructor
  · intro hP1
    have h_subset : closure (interior A) ⊆ A :=
      closure_minimal (interior_subset : interior A ⊆ A) hA_closed
    exact Set.Subset.antisymm h_subset hP1
  · intro h_eq
    simpa [h_eq] using (subset_rfl : (A : Set X) ⊆ A)

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  -- `x` is in `closure (interior (A i))`
  have hx_closure_int : x ∈ closure (interior (A i)) := (hA i) hxi
  -- `closure (interior (A i)) ⊆ closure (interior (⋃ j, A j))`
  have h_mono : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    have h_int_mono : interior (A i) ⊆ interior (⋃ j, A j) := by
      have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    exact closure_mono h_int_mono
  exact h_mono hx_closure_int

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.P3 (A i)) : Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  -- `x` lies in `interior (closure (A i))`
  have hx_int : x ∈ interior (closure (A i)) := (hA i) hxi
  -- `interior (closure (A i)) ⊆ interior (closure (⋃ j, A j))`
  have h_mono : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have h_closure_mono : closure (A i) ⊆ closure (⋃ j, A j) := by
      have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_subset
    exact interior_mono h_closure_mono
  exact h_mono hx_int

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (interior (A i))) := (hA i) hxi
  have h_mono :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    have h_closure_mono :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      have h_int_mono :
          interior (A i) ⊆ interior (⋃ j, A j) := by
        have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i, hy⟩
        exact interior_mono h_subset
      exact closure_mono h_int_mono
    exact interior_mono h_closure_mono
  exact h_mono hx_int

theorem Topology.isOpen_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1) hP3

theorem Topology.P2_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  have hP3_iff := Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  constructor
  · intro hP2
    have hP3 : Topology.P3 A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    exact (hP3_iff).1 hP3
  · intro hOpen
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.closureInterior_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior A)) := by
  have h_int_P1 : Topology.P1 (interior A) :=
    Topology.interior_satisfies_P1 (X := X) A
  exact Topology.closure_has_P1_of_P1 (X := X) (A := interior A) h_int_P1

theorem Topology.univ_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P1, Topology.P2, Topology.P3]
  simp

theorem Topology.isOpen_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.isOpen_implies_P1 (X := X) (A := A) hA,
     Topology.isOpen_implies_P2 (X := X) (A := A) hA,
     Topology.isOpen_implies_P3 (X := X) (A := A) hA⟩

theorem Topology.closureInterior_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  -- `closure (interior A)` is always contained in `closure A`
  have h₁ : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- From `P1`, `A ⊆ closure (interior A)`, hence `closure A ⊆ closure (interior A)`
  have h₂ : closure A ⊆ closure (interior A) := by
    have h : closure A ⊆ closure (closure (interior A)) :=
      closure_mono (hP1 : (A : Set X) ⊆ closure (interior A))
    simpa [closure_closure] using h
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.interiorClosure_satisfies_P2 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior (closure A)) h_open

theorem Topology.interiorClosure_satisfies_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure A)) h_open

theorem Topology.closureInteriorClosure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure A))) := by
  have hP1 : Topology.P1 (interior (closure A)) :=
    Topology.isOpen_implies_P1 (X := X) (A := interior (closure A)) isOpen_interior
  simpa using
    Topology.closure_has_P1_of_P1 (X := X) (A := interior (closure A)) hP1

theorem Topology.closureInterior_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior A) = closure A := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact Topology.closureInterior_eq_closure_of_P1 (X := X) (A := A) hP1

theorem Topology.P1_iff_closureInterior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact Topology.closureInterior_eq_closure_of_P1 (X := X) (A := A) hP1
  · intro h_eq
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this

theorem Topology.P3_closure_iff_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := closure A) h_closed)

theorem Topology.interiorClosureInterior_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior A))) ∧
    Topology.P2 (interior (closure (interior A))) ∧
    Topology.P3 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.clopen_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    IsOpen A ∧ IsClosed A := by
  have h_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hP3
  exact ⟨h_open, hA_closed⟩

theorem Topology.interiorClosure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure (interior (closure A)) := by
    exact subset_closure hx
  simpa [interior_interior] using this

theorem Topology.P2_iff_P3_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- Using existing equivalences between `P2`, `P3`, and openness for closed sets.
  have hP2 := Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  have hP3 := Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  constructor
  · intro hPA2
    -- From `P2 A` we get `IsOpen A`, then derive `P3 A`.
    have hOpen : IsOpen A := (hP2).1 hPA2
    exact (hP3).2 hOpen
  · intro hPA3
    -- From `P3 A` we get `IsOpen A`, then derive `P2 A`.
    have hOpen : IsOpen A := (hP3).1 hPA3
    exact (hP2).2 hOpen

theorem Topology.dense_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- Since `A` is dense, its closure is the whole space.
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the interior of this closure is also the whole space.
  have : (x : X) ∈ interior (closure A) := by
    simpa [hclosure] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact this)
  exact this

theorem Topology.closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  -- First inclusion: `closure (interior (closure (interior A))) ⊆ closure (interior A)`.
  have h₁ : closure (interior (closure (interior A))) ⊆ closure (interior A) := by
    have h₁' : (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    exact closure_minimal h₁' isClosed_closure
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure (interior A)))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure (interior A))) := by
    have h_temp : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    have h₂' : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using interior_mono h_temp
    exact closure_mono h₂'
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.isOpen_inter_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) ∧ Topology.P2 (A ∩ B) ∧ Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := IsOpen.inter hA hB
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := A ∩ B) hOpen

theorem Topology.clopen_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    IsOpen A ∧ IsClosed A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  exact ⟨hOpen, hA_closed⟩



theorem Topology.P2_closure_iff_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure A) h_closed)

theorem Topology.P3_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hx
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  simpa [h_open.interior_eq] using hx_closure

theorem Topology.P3_of_P2_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure A) → Topology.P3 A := by
  intro hP2
  have h_open : IsOpen (closure A) :=
    ((Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)).1) hP2
  exact Topology.P3_of_isOpen_closure (X := X) (A := A) h_open

theorem Topology.closureInteriorClosure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure A)) ⊆ closure A := by
  simpa [closure_closure] using
    (closure_mono (interior_subset : interior (closure A) ⊆ closure A))

theorem Topology.P3_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hx
  -- Since `x ∈ A`, we have `x ∈ closure A`.
  have hx_closure : (x : X) ∈ closure A := subset_closure hx
  -- From `P3 (closure A)`, we know `closure A ⊆ interior (closure (closure A))`.
  have h_subset : (closure A : Set X) ⊆ interior (closure (closure A)) := hP3
  -- Hence `x` lies in `interior (closure (closure A))`.
  have hx_int : (x : X) ∈ interior (closure (closure A)) := h_subset hx_closure
  -- But `closure (closure A)` is just `closure A`.
  simpa [closure_closure] using hx_int

theorem Topology.interiorClosureInterior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply Set.Subset.antisymm
  ·
    have h_closure_subset : closure (interior A) ⊆ A :=
      closure_minimal (interior_subset : interior A ⊆ A) hA_closed
    exact interior_mono h_closure_subset
  ·
    have h_subset : (interior A : Set X) ⊆ closure (interior A) := subset_closure
    exact interior_maximal h_subset isOpen_interior

theorem Topology.P2_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  -- Since `interior A` is dense, its closure is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Consequently, the interior of this closure is also the whole space.
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Any point of `A` is therefore in `interior (closure (interior A))`.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int] using this

theorem Topology.P2_of_denseInterior'
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : Topology.P2 A := by
  dsimp [Topology.P2]
  intro x hxA
  -- The closure of `interior A` is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence its interior is also the whole space.
  have : (x : X) ∈ interior (Set.univ : Set X) := by
    simpa [interior_univ]
  simpa [h_closure] using this

theorem Topology.dense_iff_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
      hDense.closure_eq
    have : interior (closure A) = interior ((Set.univ : Set X)) := by
      simpa [h_closure]
    simpa [interior_univ] using this
  · intro hInterior
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      have : interior (closure A) ⊆ closure A := interior_subset
      simpa [hInterior] using this
    have h_closure_eq : closure A = (Set.univ : Set X) := by
      have h_superset : closure A ⊆ (Set.univ : Set X) := by
        intro x hx
        simp
      exact Set.Subset.antisymm h_superset h_subset
    exact (dense_iff_closure_eq).2 h_closure_eq

theorem Topology.P2_closure_iff_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ Topology.P3 (closure A) := by
  simpa using
    (Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)).trans
      ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).symm)

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → Topology.P1 S) :
    Topology.P1 (⋃₀ 𝒜) := by
  dsimp [Topology.P1] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  -- From `P1` for `S`, `x` is in `closure (interior S)`.
  have hx_closure_int : (x : X) ∈ closure (interior S) :=
    (h𝒜 S hS𝒜) hxS
  -- Show that `closure (interior S)` is contained in `closure (interior (⋃₀ 𝒜))`.
  have h_incl : closure (interior S) ⊆ closure (interior (⋃₀ 𝒜)) := by
    -- First, upgrade the inclusion on the level of interiors.
    have h_subset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
      intro y hy
      exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
    have h_int : interior S ⊆ interior (⋃₀ 𝒜) :=
      interior_mono h_subset
    -- Taking closures yields the desired inclusion.
    exact closure_mono h_int
  exact h_incl hx_closure_int

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → Topology.P3 S) :
    Topology.P3 (⋃₀ 𝒜) := by
  dsimp [Topology.P3] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  -- From `P3` for `S`, `x` lies in `interior (closure S)`.
  have hx_int : (x : X) ∈ interior (closure S) := (h𝒜 S hS𝒜) hxS
  -- Show `interior (closure S)` is contained in `interior (closure (⋃₀ 𝒜))`.
  have h_incl : interior (closure S) ⊆ interior (closure (⋃₀ 𝒜)) := by
    -- First, upgrade the inclusion on the level of closures.
    have h_closure_mono : closure S ⊆ closure (⋃₀ 𝒜) := by
      have h_subset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
        intro y hy
        exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
      exact closure_mono h_subset
    -- Taking interiors yields the desired inclusion.
    exact interior_mono h_closure_mono
  exact h_incl hx_int

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → Topology.P2 S) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2] at h𝒜 ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨S, hS𝒜, hxS⟩
  -- From `P2` for `S`, we know `x` lies in `interior (closure (interior S))`.
  have hx_int : (x : X) ∈ interior (closure (interior S)) := (h𝒜 S hS𝒜) hxS
  -- Show that `interior (closure (interior S)) ⊆ interior (closure (interior (⋃₀ 𝒜)))`.
  have h_incl : interior (closure (interior S)) ⊆
      interior (closure (interior (⋃₀ 𝒜))) := by
    -- We first show `closure (interior S) ⊆ closure (interior (⋃₀ 𝒜))`.
    have h_closure_mono : closure (interior S) ⊆ closure (interior (⋃₀ 𝒜)) := by
      -- This follows from `interior S ⊆ interior (⋃₀ 𝒜)`.
      have h_int_mono : interior S ⊆ interior (⋃₀ 𝒜) := by
        have h_subset : (S : Set X) ⊆ ⋃₀ 𝒜 := by
          intro y hy
          exact Set.mem_sUnion.2 ⟨S, hS𝒜, hy⟩
        exact interior_mono h_subset
      exact closure_mono h_int_mono
    -- Taking interiors yields the desired inclusion.
    exact interior_mono h_closure_mono
  exact h_incl hx_int

theorem Topology.closureInteriorClosure_subset_closure' {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  have h : interior (closure A) ⊆ closure A := interior_subset
  simpa [closure_closure] using closure_mono h

theorem Topology.P1_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 A := by
  intro hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  exact Topology.P2_implies_P1 (X := X) (A := A) hP2

theorem Topology.P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 A := by
  intro hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  exact Topology.P2_implies_P3 (X := X) (A := A) hP2

theorem Topology.interiorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h_closure_subset : closure (interior (closure A)) ⊆ closure A := by
      have h_int_subset : (interior (closure A) : Set X) ⊆ closure A :=
        interior_subset
      exact closure_minimal h_int_subset isClosed_closure
    exact interior_mono h_closure_subset
  ·
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    have h_subset : (interior (closure A) : Set X) ⊆
        closure (interior (closure A)) := subset_closure
    exact interior_maximal h_subset h_open

theorem Topology.P1_iff_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _
    dsimp [Topology.P2]
    have h_subset : (A : Set X) ⊆ interior (closure A) :=
      interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA
    simpa [hA.interior_eq] using h_subset
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2

theorem Topology.closureInteriorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closureInterior_idempotent (X := X) (A := closure A))

theorem Topology.P1_iff_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  simpa using h₁.trans h₂

theorem Topology.closureInterior_iterate_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  -- First, apply the idempotence lemma to `closure (interior A)`.
  have hStep1 :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closureInterior_idempotent (X := X) (A := closure (interior A)))
  -- Next, apply the idempotence lemma to `A` itself.
  have hStep2 :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closureInterior_idempotent (X := X) (A := A))
  -- Combining the two equalities yields the desired result.
  simpa using (hStep1.trans hStep2)

theorem Topology.P2_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) : Topology.P2 (closure A) := by
  exact ((Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)).2) h_open

theorem Topology.closure_has_P1_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 (closure A) := by
  have hP1A : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA
  exact Topology.closure_has_P1_of_P1 (X := X) (A := A) hP1A

theorem Topology.closureInterior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact closure_mono h

theorem Topology.interiorClosure_iterate_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First reduction using idempotence on `interior (closure A)`.
  have hStep1 :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      (Topology.interiorClosure_idempotent (X := X) (A := interior (closure A)))
  -- Second reduction using idempotence on `A`.
  have hStep2 :
      interior (closure (interior (closure A))) = interior (closure A) := by
    simpa using
      (Topology.interiorClosure_idempotent (X := X) (A := A))
  -- Combine the two equalities.
  simpa using (hStep1.trans hStep2)

theorem Topology.interior_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  simpa using
    (Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := interior A) isOpen_interior)

theorem Topology.P2_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P2 (closure (A : Set X)) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space, which is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have h_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
    simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Apply the lemma that an open closure guarantees `P2`.
  exact (Topology.P2_of_isOpen_closure (X := X) (A := A)) hOpen

theorem Topology.interiorClosureClosure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  apply Set.Subset.antisymm
  ·
    have h_subset : closure A ⊆ closure (interior A) := by
      have h : (closure A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono (hP1 : (A : Set X) ⊆ closure (interior A))
      simpa [closure_closure] using h
    exact interior_mono h_subset
  ·
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono h_subset

theorem Topology.P3_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 (closure (A : Set X)) := by
  intro hDense
  dsimp [Topology.P3]
  intro x hx
  -- Since `A` is dense, its closure is the whole space.
  have h_closure_eq : closure (A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence every point lies in the interior of this closure (and of its
  -- further closure, which is equal to itself).
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [closure_closure, h_closure_eq, interior_univ] using this

theorem Topology.P1_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  have hOpen : IsOpen A :=
    (Topology.clopen_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3).1
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact
    Topology.interiorClosure_eq_interiorClosureInterior_of_P1
      (X := X) (A := A) hP1

theorem Topology.interiorClosureInterior_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact interior_mono h_closure

theorem Topology.P3_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hA_P3 : Topology.P3 A) (hB_P3 : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- From `P3` and closedness, both `A` and `B` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hA_P3
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB_closed).1 hB_P3
  -- The intersection of two open sets is open.
  have hAB_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- An open set automatically satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A ∩ B) hAB_open

theorem Topology.P1_of_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ closure (interior A)) :
    Topology.P1 B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- First, `x` lies in `closure (interior A)` by assumption.
  have hx_closure_intA : (x : X) ∈ closure (interior A) := hBsubset hxB
  -- Since `interior A ⊆ interior B`, we have
  -- `closure (interior A) ⊆ closure (interior B)`.
  have h_enlarge : closure (interior A) ⊆ closure (interior B) := by
    have h_int_mono : (interior A : Set X) ⊆ interior B :=
      interior_mono hAB
    exact closure_mono h_int_mono
  -- Hence `x` lies in `closure (interior B)`, as required.
  exact h_enlarge hx_closure_intA

theorem Topology.closure_has_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hDense
  have h_eq : (closure (A : Set X) : Set X) = Set.univ := hDense.closure_eq
  dsimp [Topology.P1]
  intro x hx
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simpa [h_eq] using hx
  simpa [h_eq, interior_univ] using hx_univ

theorem Topology.closureInteriorClosure_eq_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    closure (interior (closure A)) = closure (interior A) := by
  -- First inclusion: `closure (interior (closure A)) ⊆ closure (interior A)`.
  have h_closureA_subset : (closure A : Set X) ⊆ closure (interior A) := by
    -- From `P1`, we know `A ⊆ closure (interior A)`.  Taking closures yields
    -- `closure A ⊆ closure (closure (interior A)) = closure (interior A)`.
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono (hP1 : (A : Set X) ⊆ closure (interior A))
    simpa [closure_closure] using this
  have h_int_subset : (interior (closure A) : Set X) ⊆ closure (interior A) :=
    Set.Subset.trans
      (interior_subset : interior (closure A) ⊆ closure A)
      h_closureA_subset
  have h₁ : closure (interior (closure A)) ⊆ closure (interior A) :=
    closure_minimal h_int_subset isClosed_closure
  -- Second inclusion: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closureInterior_subset_closureInteriorClosure (X := X) (A := A)
  -- Combine the two inclusions.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.interiorClosure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (A : Set X)) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem Topology.interiorClosureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interiorClosure_idempotent (X := X) (A := interior A))

theorem Topology.interiorClosure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) ∧
      Topology.P2 (interior (closure A)) ∧
      Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := interior (closure A)) hOpen

theorem Topology.closureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x` lies in `closure (interior A)`
  have hxA : (x : X) ∈ closure (interior A) := by
    -- `interior (A ∩ B)` is contained in `interior A`
    have h_intA : (interior (A ∩ B) : Set X) ⊆ interior A := by
      exact interior_mono (by
        intro y hy
        exact hy.1)
    exact (closure_mono h_intA) hx
  -- Show `x` lies in `closure (interior B)`
  have hxB : (x : X) ∈ closure (interior B) := by
    -- `interior (A ∩ B)` is contained in `interior B`
    have h_intB : (interior (A ∩ B) : Set X) ⊆ interior B := by
      exact interior_mono (by
        intro y hy
        exact hy.2)
    exact (closure_mono h_intB) hx
  exact And.intro hxA hxB

theorem Topology.closureInterior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.interiorClosureInterior_subset_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  exact interior_subset

theorem Topology.interiorClosure_subset_interiorClosure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B)) := by
  have h_subset : (A : Set X) ⊆ (A ∪ B) := by
    intro x hx
    exact Or.inl hx
  exact
    Topology.interiorClosure_mono (X := X) (A := A) (B := A ∪ B) h_subset

theorem Topology.P1_closure_iff_closureInterior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (interior (closure A)) = closure A := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P1_iff_closureInterior_eq_of_isClosed
      (X := X) (A := closure A) hClosed)

theorem Topology.P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 (Aᶜ) := by
  -- The complement of a closed set is open.
  have h_open : IsOpen (Aᶜ) := by
    simpa using hA_closed.isOpen_compl
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := Aᶜ) h_open

theorem Topology.interior_eq_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    interior A = A := by
  -- From `P2` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  -- For an open set, the interior equals the set itself.
  simpa using hOpen.interior_eq

theorem Topology.P2_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P2 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.isOpen_implies_P2 (X := X) (A := Aᶜ) h_open

theorem Topology.P1_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P1 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.isOpen_implies_P1 (X := X) (A := Aᶜ) h_open

theorem Topology.P2_inter_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hA_P2 : Topology.P2 A) (hB_P2 : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- From `P2` and closedness we deduce that both `A` and `B` are open.
  have hA_open : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hA_P2
  have hB_open : IsOpen B :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := B) hB_closed hB_P2
  -- The intersection of two open sets is open.
  have hAB_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A ∩ B) hAB_open

theorem Topology.P3_iff_P1_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P3 A ↔ Topology.P1 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_denseInterior (X := X) (A := A) hDense
  have hP3 : Topology.P3 A :=
    Topology.P3_of_denseInterior (X := X) (A := A) hDense
  exact ⟨fun _ => hP1, fun _ => hP3⟩

theorem Topology.P2_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  simpa using
    (Topology.P2_iff_P3_of_isOpen (X := X) (A := Aᶜ) h_open)

theorem Topology.closureInteriorClosure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  intro hDense
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence the interior of this closure is also the whole space.
  have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- Taking the closure again yields the whole space.
  simpa [h_int, closure_univ]

theorem Topology.closureInterior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (A : Set X) := by
  simpa using
    closure_mono (interior_subset : interior A ⊆ A)

theorem Topology.P2_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure A) := by
  intro hP3
  exact ((Topology.P2_closure_iff_P3_closure (X := X) (A := A)).2) hP3

theorem Topology.interiorClosure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → interior (closure A) = (Set.univ : Set X) := by
  intro hDense
  exact
    (Topology.dense_iff_interiorClosure_eq_univ
      (X := X) (A := A)).1 hDense

theorem Topology.P1_iff_P2_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P2 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := Aᶜ) h_open)

theorem Topology.compl_satisfies_P1_P2_P3_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  have hOpen : IsOpen (Aᶜ) := hA_closed.isOpen_compl
  exact Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := Aᶜ) hOpen

theorem Topology.interiorClosure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each `i`, show `x ∈ interior (closure (A i))`.
  have h_each : ∀ i, (x : X) ∈ interior (closure (A i)) := by
    intro i
    -- The intersection is contained in `A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `closure` and `interior`.
    have h_closure_mono : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset
    have h_int_mono : interior (closure (⋂ j, A j)) ⊆
        interior (closure (A i)) := interior_mono h_closure_mono
    exact h_int_mono hx
  exact Set.mem_iInter.2 h_each

theorem Topology.dense_of_denseInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure (A : Set X))) → Dense (A : Set X) := by
  intro hDense
  -- The closure of `interior (closure A)` is the whole space.
  have h_univ : closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- `closure (interior (closure A))` is contained in `closure A`.
  have h_subset : closure (interior (closure (A : Set X))) ⊆ closure A := by
    have h₀ : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    have h₁ :
        closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
      closure_mono h₀
    simpa [closure_closure] using h₁
  -- Hence `closure A` is the whole space.
  have h_closureA : closure (A : Set X) = (Set.univ : Set X) := by
    have h2 : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_univ] using h_subset
    have h3 : closure A ⊆ (Set.univ : Set X) := by
      intro x hx
      simp
    exact Set.Subset.antisymm h3 h2
  -- Conclude that `A` is dense.
  exact (dense_iff_closure_eq).2 h_closureA

theorem Topology.interiorClosure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show that `x ∈ interior (closure A)`.
  have hxA : (x : X) ∈ interior (closure A) := by
    -- Since `A ∩ B ⊆ A`, taking closures preserves the inclusion.
    have h_sub : closure (A ∩ B) ⊆ closure A := by
      have h₀ : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact closure_mono h₀
    -- Monotonicity of `interior` then gives the desired inclusion.
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure A) :=
      interior_mono h_sub
    exact h_int hx
  -- Show that `x ∈ interior (closure B)`.
  have hxB : (x : X) ∈ interior (closure B) := by
    -- Since `A ∩ B ⊆ B`, taking closures preserves the inclusion.
    have h_sub : closure (A ∩ B) ⊆ closure B := by
      have h₀ : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact closure_mono h₀
    -- Apply monotonicity of `interior` again.
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure B) :=
      interior_mono h_sub
    exact h_int hx
  exact And.intro hxA hxB

theorem Topology.closure_has_P1_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 (closure A) := by
  intro hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  exact Topology.closure_has_P1_of_P2 (X := X) (A := A) hP2

theorem Topology.closureInterior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior A` is contained in `interior (A ∪ B)`.
      have h_int_mono : interior A ⊆ interior (A ∪ B) := by
        have h_subset : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono h_subset
      -- Taking closures preserves the inclusion.
      have h_closure_mono : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_mono
      exact h_closure_mono hxA
  | inr hxB =>
      -- `interior B` is contained in `interior (A ∪ B)`.
      have h_int_mono : interior B ⊆ interior (A ∪ B) := by
        have h_subset : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono h_subset
      -- Taking closures preserves the inclusion.
      have h_closure_mono : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_int_mono
      exact h_closure_mono hxB

theorem Topology.interiorClosure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `closure A ⊆ closure (A ∪ B)`
      have h_closure_mono : closure A ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact closure_mono this
      -- Taking interiors preserves the inclusion.
      have h_int_mono : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxA
  | inr hxB =>
      -- `closure B ⊆ closure (A ∪ B)`
      have h_closure_mono : closure B ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact closure_mono this
      -- Taking interiors preserves the inclusion.
      have h_int_mono : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxB

theorem Topology.P2_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P2 A := by
  -- From `P3` and closedness we know that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.clopen_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3).1
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.closureInterior_isClosed
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure : IsClosed (closure (interior A)))

theorem Topology.P1_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    Topology.P1 A := by
  -- From `P2` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  -- Any open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem Topology.P3_closureInterior_iff_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := closure (interior A)) h_closed)

theorem Topology.interior_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.Subset_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hB : Topology.P1 B) :
    (A : Set X) ⊆ closure (interior B) := by
  dsimp [Topology.P1] at hB
  exact Set.Subset.trans hAB hB

theorem Topology.interiorClosureInterior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First, use the monotonicity of `interior` to upgrade the inclusion.
  have hInt : interior A ⊆ interior B :=
    interior_mono hAB
  -- Taking closures preserves the inclusion.
  have hClos : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hInt
  -- Finally, apply monotonicity of `interior` once more.
  exact interior_mono hClos

theorem Topology.P1_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  have h₁ := Topology.P1_iff_P2_compl_of_isClosed (X := X) (A := A) hA_closed
  have h₂ := Topology.P2_iff_P3_compl_of_isClosed (X := X) (A := A) hA_closed
  simpa using h₁.trans h₂

theorem Topology.P3_of_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- From the assumption, `x` lies in `interior (closure A)`.
  have hx_intA : (x : X) ∈ interior (closure A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_closure_mono : closure A ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves this inclusion.
  have h_int_mono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure_mono
  -- Combining the facts gives the desired result.
  exact h_int_mono hx_intA

theorem Topology.dense_of_closureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Dense (A : Set X) := by
  intro hClosureInt
  -- First, show that `closure A = univ`.
  have hSubset : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    -- Since `interior A ⊆ A`, taking closures yields
    -- `closure (interior A) ⊆ closure A`.
    have hIncl : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [hClosureInt] using hIncl
  have hSuperset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro x _hx
    simp
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm hSuperset hSubset
  exact (dense_iff_closure_eq).2 hClosureA

theorem Topology.denseInterior_iff_interiorClosureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔
      interior (closure (interior A)) = (Set.univ : Set X) := by
  simpa using
    (Topology.dense_iff_interiorClosure_eq_univ (X := X) (A := interior A))

theorem Topology.closureInterior_satisfies_P2_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P2 (closure (interior A)) := by
  -- The closure of `interior A` is the whole space.
  have h_eq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence `closure (interior A)` is open.
  have h_open : IsOpen (closure (interior A)) := by
    simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := closure (interior A)) h_open

theorem Topology.P2_closureInterior_iff_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior A)) h_closed)

theorem Topology.union_interior_subset_interior_union'
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A` is contained in `interior (A ∪ B)` by monotonicity.
      have h_mono : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      have h_int_mono : interior A ⊆ interior (A ∪ B) := interior_mono h_mono
      exact h_int_mono hA
  | inr hB =>
      -- `interior B` is contained in `interior (A ∪ B)` by monotonicity.
      have h_mono : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have h_int_mono : interior B ⊆ interior (A ∪ B) := interior_mono h_mono
      exact h_int_mono hB

theorem Topology.interiorClosure_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem Topology.P3_union_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB : IsOpen B) :
    Topology.P3 (A ∪ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- Case `x ∈ A`
      have hxA_int : (x : X) ∈ interior (closure A) := hA hxA
      have h_closure_mono : closure A ⊆ closure (A ∪ B) := by
        have : (A : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inl hy
        exact closure_mono this
      have h_int_mono :
          interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxA_int
  | inr hxB =>
      -- Case `x ∈ B`
      have h_subset : (B : Set X) ⊆ interior (closure B) :=
        interior_maximal (subset_closure : (B : Set X) ⊆ closure B) hB
      have hxB_int : (x : X) ∈ interior (closure B) := h_subset hxB
      have h_closure_mono : closure B ⊆ closure (A ∪ B) := by
        have : (B : Set X) ⊆ A ∪ B := by
          intro y hy; exact Or.inr hy
        exact closure_mono this
      have h_int_mono :
          interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono h_closure_mono
      exact h_int_mono hxB_int

theorem Topology.P1_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P1 (closure A) := by
  intro hP3
  have hOpen : IsOpen (closure (A : Set X)) :=
    (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1 hP3
  exact Topology.isOpen_implies_P1 (X := X) (A := closure A) hOpen

theorem Topology.P2_of_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ interior (closure (interior A))) :
    Topology.P2 B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- From the assumption, `x` lies in `interior (closure (interior A))`.
  have hxA : (x : X) ∈ interior (closure (interior A)) := hBsubset hxB
  -- We now show that
  -- `interior (closure (interior A)) ⊆ interior (closure (interior B))`.
  have h_mono :
      interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
    -- Monotonicity of `interior` with respect to set inclusion.
    have h_int : interior A ⊆ interior B := interior_mono hAB
    -- Taking closures preserves inclusion.
    have h_closure : closure (interior A) ⊆ closure (interior B) :=
      closure_mono h_int
    -- Finally, apply monotonicity of `interior` once more.
    exact interior_mono h_closure
  -- Combining the two facts yields the desired result.
  exact h_mono hxA

theorem Topology.isOpen_union_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∪ B) ∧ Topology.P2 (A ∪ B) ∧ Topology.P3 (A ∪ B) := by
  have hOpen : IsOpen (A ∪ B) := IsOpen.union hA hB
  simpa using
    Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A ∪ B) hOpen

theorem Topology.P2_union_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB : IsOpen B) : Topology.P2 (A ∪ B) := by
  have hB_P2 : Topology.P2 B :=
    Topology.isOpen_implies_P2 (X := X) (A := B) hB
  exact Topology.P2_union (X := X) (A := A) (B := B) hA hB_P2

theorem Topology.P2_union_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : Topology.P2 B) : Topology.P2 (A ∪ B) := by
  -- Since `A` is open, it satisfies `P2`.
  have hA_P2 : Topology.P2 A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hA
  -- Apply the existing `P2_union` lemma.
  exact Topology.P2_union (X := X) (A := A) (B := B) hA_P2 hB

theorem Topology.closureInterior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem Topology.P1_union_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : IsOpen B) : Topology.P1 (A ∪ B) := by
  -- Since `B` is open, it satisfies `P1`.
  have hB_P1 : Topology.P1 B :=
    Topology.isOpen_implies_P1 (X := X) (A := B) hB
  -- Apply the existing `P1_union` lemma.
  exact Topology.P1_union (X := X) (A := A) (B := B) hA hB_P1

theorem Topology.P3_inter_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 A) (hB_open : IsOpen B) :
    Topology.P3 (A ∩ B) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  have hxA_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Define an auxiliary open set around `x`.
  have h_open_aux : IsOpen (B ∩ interior (closure A)) :=
    IsOpen.inter hB_open isOpen_interior
  -- This open set is contained in `closure (A ∩ B)`.
  have h_subset_aux :
      (B ∩ interior (closure A) : Set X) ⊆ closure (A ∩ B) := by
    intro y hy
    rcases hy with ⟨hyB, hyIntA⟩
    -- `y` lies in `B` and in `interior (closure A)`, hence in `closure A`.
    have hy_closureA : (y : X) ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hyIntA
    -- Show that every neighbourhood of `y` meets `A ∩ B`.
    have : (y : X) ∈ closure (A ∩ B) := by
      refine (mem_closure_iff).2 ?_
      intro U hU hyU
      -- `U ∩ B` is an open neighbourhood of `y`.
      have hUB_open : IsOpen (U ∩ B) := IsOpen.inter hU hB_open
      have hyUB : (y : X) ∈ U ∩ B := And.intro hyU hyB
      -- Since `y ∈ closure A`, `U ∩ B` meets `A`.
      have h_nonempty : ((U ∩ B) ∩ A).Nonempty :=
        (mem_closure_iff).1 hy_closureA (U ∩ B) hUB_open hyUB
      -- Rewriting gives a point in `U ∩ (A ∩ B)`.
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h_nonempty
    exact this
  -- The auxiliary open set lies inside the interior of the target closure.
  have h_aux_incl :
      (B ∩ interior (closure A) : Set X) ⊆ interior (closure (A ∩ B)) :=
    interior_maximal h_subset_aux h_open_aux
  -- Since `x` belongs to this auxiliary open set, it belongs to the target interior.
  have hx_aux : (x : X) ∈ B ∩ interior (closure A) :=
    And.intro hxB hxA_int
  exact h_aux_incl hx_aux

theorem Topology.P1_union_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  have hA_P1 : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA_open
  exact Topology.P1_union (X := X) (A := A) (B := B) hA_P1 hB

theorem Topology.P3_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Reuse the existing lemma with the roles of `A` and `B` swapped.
  have h : Topology.P3 (B ∩ A) :=
    Topology.P3_inter_isOpen_right (X := X) (A := B) (B := A) hB hA_open
  simpa [Set.inter_comm] using h

theorem Topology.P2_inter_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_open : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- `x` lies in `interior (closure (interior A))` by `P2 A`.
  have hxA_int : (x : X) ∈ interior (closure (interior A)) := hA hxA
  -- Auxiliary open set around `x`.
  have h_open_aux :
      IsOpen (B ∩ interior (closure (interior A))) :=
    IsOpen.inter hB_open isOpen_interior
  -- This auxiliary set is contained in `closure (interior (A ∩ B))`.
  have h_subset_aux :
      (B ∩ interior (closure (interior A)) : Set X) ⊆
        closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hyB, hyIntA⟩
    -- `y` lies in the closure of `interior A`.
    have hy_closureA : (y : X) ∈ closure (interior A) :=
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A)) hyIntA
    -- Show that every neighbourhood of `y` meets `interior (A ∩ B)`.
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      refine (mem_closure_iff).2 ?_
      intro U hU hyU
      -- `U ∩ B` is an open neighbourhood of `y`.
      have hUB_open : IsOpen (U ∩ B) := IsOpen.inter hU hB_open
      have hyUB : (y : X) ∈ U ∩ B := ⟨hyU, hyB⟩
      -- Since `y ∈ closure (interior A)`, `U ∩ B` meets `interior A`.
      have h_nonempty : ((U ∩ B) ∩ interior A).Nonempty :=
        ((mem_closure_iff).1 hy_closureA) (U ∩ B) hUB_open hyUB
      -- A point in this intersection lies in `interior (A ∩ B)`.
      rcases h_nonempty with ⟨z, ⟨hzU, hzB⟩, hzIntA⟩
      -- `interior A ∩ B` is an open subset of `A ∩ B`, hence contained in its interior.
      have hz_interior : (z : X) ∈ interior (A ∩ B) := by
        have h_open : IsOpen (interior A ∩ B) :=
          IsOpen.inter isOpen_interior hB_open
        have h_subset :
            (interior A ∩ B : Set X) ⊆ A ∩ B := by
          intro w hw; exact ⟨interior_subset hw.1, hw.2⟩
        have h_interior_max :=
          interior_maximal h_subset h_open
        exact h_interior_max ⟨hzIntA, hzB⟩
      -- Finally, `z` witnesses that `U` meets `interior (A ∩ B)`.
      refine ⟨z, hzU, hz_interior⟩
    exact this
  -- The auxiliary open set lies inside the desired interior.
  have h_aux_incl :
      (B ∩ interior (closure (interior A)) : Set X) ⊆
        interior (closure (interior (A ∩ B))) :=
    interior_maximal h_subset_aux h_open_aux
  -- Since `x` belongs to the auxiliary open set, it belongs to the target interior.
  have hx_aux : (x : X) ∈ B ∩ interior (closure (interior A)) :=
    ⟨hxB, hxA_int⟩
  exact h_aux_incl hx_aux

theorem Topology.P2_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  simpa [Set.inter_comm] using
    (Topology.P2_inter_isOpen_right (X := X) (A := B) (B := A) hB hA_open)

theorem Topology.interiorClosure_subset_interiorClosure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B)) := by
  have h_subset : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  exact Topology.interiorClosure_mono (X := X) (A := B) (B := A ∪ B) h_subset

theorem Topology.P1_inter_isOpen_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB_open : IsOpen B) : Topology.P1 (A ∩ B) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  have hx_closure_intA : (x : X) ∈ closure (interior A) := hA hxA
  -- We first show `closure (interior A) ∩ B ⊆ closure (interior (A ∩ B))`.
  have h_subset :
      closure (interior A) ∩ B ⊆ closure (interior (A ∩ B)) := by
    intro y hy
    rcases hy with ⟨hy_closureA, hyB⟩
    -- Use the neighborhood characterization of closure.
    have : (y : X) ∈ closure (interior (A ∩ B)) := by
      apply (mem_closure_iff).2
      intro U hU hUy
      -- Consider the open set `U ∩ B`, which contains `y`.
      have hV_open : IsOpen (U ∩ B) := IsOpen.inter hU hB_open
      have hVy : (y : X) ∈ U ∩ B := ⟨hUy, hyB⟩
      -- Since `y ∈ closure (interior A)`, this set meets `interior A`.
      have h_nonempty :
          ((U ∩ B) ∩ interior A).Nonempty :=
        ((mem_closure_iff).1 hy_closureA) (U ∩ B) hV_open hVy
      rcases h_nonempty with ⟨z, hzV, hzIntA⟩
      -- `z` lies in `interior A ∩ B`, which is open and contained in `A ∩ B`.
      have hz_interior_AB : (z : X) ∈ interior (A ∩ B) := by
        have h_open : IsOpen (interior A ∩ B) :=
          IsOpen.inter isOpen_interior hB_open
        have h_sub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
          intro w hw; exact ⟨interior_subset hw.1, hw.2⟩
        have h_max := interior_maximal h_sub h_open
        exact h_max ⟨hzIntA, hzV.2⟩
      have hzU : (z : X) ∈ U := hzV.1
      exact ⟨z, hzU, hz_interior_AB⟩
    exact this
  -- Apply the inclusion to `x`, which belongs to the left-hand side.
  have hx_in : (x : X) ∈ closure (interior A) ∩ B := ⟨hx_closure_intA, hxB⟩
  exact h_subset hx_in

theorem Topology.P1_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P1 B) :
    Topology.P1 (A ∩ B) := by
  -- Apply the existing lemma with swapped roles and rewrite the intersection.
  have h := Topology.P1_inter_isOpen_right (X := X) (A := B) (B := A) hB hA_open
  simpa [Set.inter_comm] using h

theorem Topology.closureInterior_satisfies_P3_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure (interior A)) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have h_eq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence `closure (interior A)` is open.
  have h_open : IsOpen (closure (interior A)) := by
    simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3
    (X := X) (A := closure (interior A)) h_open

theorem Topology.P3_closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (interior (closure (interior A)))) ↔
      Topology.P3 (closure (interior A)) := by
  -- Use the idempotence of the `closure ∘ interior` operator.
  have hEq :
      (closure (interior (closure (interior A))) : Set X) =
        closure (interior A) :=
    Topology.closureInterior_idempotent (X := X) (A := A)
  constructor
  · intro hP3
    simpa [hEq] using hP3
  · intro hP3
    simpa [hEq] using hP3

theorem Topology.P2_iff_P1_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P2 A ↔ Topology.P1 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_denseInterior (X := X) (A := A) hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  exact ⟨fun _ => hP1, fun _ => hP2⟩

theorem Topology.P2_iff_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  have h₁ := Topology.P2_iff_P1_of_denseInterior (X := X) (A := A) hDense
  have h₂ := Topology.P3_iff_P1_of_dense (X := X) (A := A) hDense
  simpa using h₁.trans h₂.symm

theorem Topology.P3_union_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen A) (hB : Topology.P3 B) :
    Topology.P3 (A ∪ B) := by
  have h :=
    Topology.P3_union_isOpen_right (X := X) (A := B) (B := A) hB hA_open
  simpa [Set.union_comm] using h

theorem Topology.interiorClosure_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA_closed.closure_eq]

theorem Topology.isOpen_of_isClosed_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (interior A)) :
    IsOpen A := by
  -- From density of `interior A`, we obtain `P2 A`.
  have hP2 : Topology.P2 A :=
    Topology.P2_of_denseInterior (X := X) (A := A) hDense
  -- A closed set satisfying `P2` is open.
  exact Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2

theorem Topology.denseInteriorClosure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Dense (interior (closure (A : Set X))) := by
  intro hDense
  -- From the density of `A`, we know `closure (interior (closure A)) = univ`.
  have h_closure :
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    Topology.closureInteriorClosure_eq_univ_of_dense (X := X) (A := A) hDense
  -- Conclude density via the closure characterization.
  exact (dense_iff_closure_eq).2 h_closure

theorem Topology.closureInterior_eq_univ_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → closure (interior A) = (Set.univ : Set X) := by
  intro hDense
  simpa using hDense.closure_eq

theorem Topology.dense_iff_denseInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ Dense (interior (closure (A : Set X))) := by
  constructor
  · intro hDense
    exact Topology.denseInteriorClosure_of_dense (X := X) (A := A) hDense
  · intro hDenseInt
    exact Topology.dense_of_denseInteriorClosure (X := X) (A := A) hDenseInt

theorem Topology.denseInterior_iff_closureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ closure (interior A) = (Set.univ : Set X) := by
  simpa using (dense_iff_closure_eq (s := (interior A : Set X)))

theorem Topology.closureInteriorClosure_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      closure (interior (closure A)) = closure A := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    exact Topology.closureInteriorClosure_subset_closure (X := X) (A := A)
  ·
    have : (closure A : Set X) ⊆ closure (interior (closure A)) := by
      -- From `P3` we have `A ⊆ interior (closure A)`.
      have h_subset : (A : Set X) ⊆ interior (closure A) := hP3
      -- Taking closures preserves inclusions.
      exact closure_mono h_subset
    simpa using this

theorem Topology.interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  -- `A ∩ B` is contained in `A`, hence their interiors satisfy the same relation.
  have hA : (x : X) ∈ interior A := by
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    exact (interior_mono h_subset) hx
  -- Similarly, `A ∩ B` is contained in `B`.
  have hB : (x : X) ∈ interior B := by
    have h_subset : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (interior_mono h_subset) hx
  exact And.intro hA hB

theorem Topology.closureInterior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, hence in `∅`.
    have h_subset : (interior A : Set X) ⊆ (∅ : Set X) := by
      have : (interior A : Set X) ⊆ closure (interior A) :=
        subset_closure
      simpa [h] using this
    have h_eq : (interior A : Set X) = (∅ : Set X) := by
      exact Set.Subset.antisymm h_subset (by simp)
    simpa using h_eq
  · intro h
    simpa [h, closure_empty]

theorem Topology.P3_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    Topology.P3 A := by
  -- A closed set satisfying `P2` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem Topology.P2_iff_P3_compl_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_open : IsOpen A) :
    Topology.P2 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  -- The complement of an open set is closed.
  have h_closed : IsClosed (Aᶜ) := by
    simpa using hA_open.isClosed_compl
  -- Apply the existing equivalence for closed sets.
  simpa using
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := Aᶜ) h_closed)

theorem Topology.interior_compl_eq_empty_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → interior (Aᶜ) = (∅ : Set X) := by
  intro hDense
  classical
  -- We prove every point is *not* in `interior (Aᶜ)`.
  apply (Set.eq_empty_iff_forall_not_mem).2
  intro x hxInt
  -- Since `A` is dense, the closure of `A` is the whole space, hence `x ∈ closure A`.
  have hx_closure : (x : X) ∈ closure (A : Set X) := by
    have hClosure : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
    simpa [hClosure] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact this)
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  have h_open : IsOpen (interior (Aᶜ)) := isOpen_interior
  -- By density, this neighbourhood must meet `A`.
  have h_inter : ((interior (Aᶜ)) ∩ A).Nonempty :=
    (mem_closure_iff).1 hx_closure (interior (Aᶜ)) h_open hxInt
  -- But `interior (Aᶜ)` is contained in `Aᶜ`, contradicting the intersection with `A`.
  rcases h_inter with ⟨y, hyInt, hyA⟩
  have hyNotA : (y : X) ∈ Aᶜ := interior_subset hyInt
  exact (hyNotA hyA).elim

theorem Topology.closureInterior_iterate_idempotent₂
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, apply the three–step idempotence lemma to `closure (interior A)`.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closureInterior_iterate_idempotent
        (X := X) (A := closure (interior A)))
  -- Next, reduce the right‐hand side using the basic idempotence lemma.
  have h₂ :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using
      (Topology.closureInterior_idempotent (X := X) (A := A))
  -- Combine the two equalities to obtain the desired result.
  simpa using h₁.trans h₂

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∪ B) = interior (A ∪ B) := rfl

theorem Topology.closureInterior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- For each `i`, we will show `x ∈ closure (interior (A i))`.
  have h_each : ∀ i, (x : X) ∈ closure (interior (A i)) := by
    intro i
    -- `interior (⋂ i, A i)` is contained in `interior (A i)`.
    have h_int_subset : interior (⋂ j, A j) ⊆ interior (A i) := by
      have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
        intro y hy
        exact (Set.mem_iInter.1 hy) i
      exact interior_mono h_subset
    -- Taking closures preserves this inclusion.
    have h_closure_subset :
        closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) :=
      closure_mono h_int_subset
    exact h_closure_subset hx
  -- Conclude that `x` lies in the intersection of all these closures.
  exact Set.mem_iInter.2 h_each

theorem Topology.dense_iff_eq_univ_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Dense (A : Set X) ↔ (A : Set X) = Set.univ := by
  have h_closure : closure (A : Set X) = A := hA_closed.closure_eq
  have h_dense :
      Dense (A : Set X) ↔ closure (A : Set X) = (Set.univ : Set X) :=
    dense_iff_closure_eq (s := (A : Set X))
  simpa [h_closure] using h_dense

theorem Topology.P1_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) :
    Topology.P1 (A ∪ B ∪ C) := by
  -- First, obtain `P1` for `A ∪ B`.
  have hAB : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P1 ((A ∪ B) ∪ C) :=
    Topology.P1_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left-associative) form.
  simpa [Set.union_assoc] using hABC

theorem Topology.P2_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) :
    Topology.P2 (A ∪ B ∪ C) := by
  -- First, obtain `P2` for `A ∪ B`.
  have hAB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left-associative) form.
  simpa [Set.union_assoc] using hABC

theorem Topology.P1_closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (interior A)))) ↔
      Topology.P1 (closure (interior A)) := by
  -- `closure ∘ interior` is idempotent, hence the two sets coincide.
  have hEq :
      (closure (interior (closure (interior A))) : Set X) =
        closure (interior A) :=
    Topology.closureInterior_idempotent (X := X) (A := A)
  -- After rewriting with this equality, both sides are definitionally equal.
  simpa [hEq] using
    (Iff.rfl :
      Topology.P1 (closure (interior (closure (interior A)))) ↔
        Topology.P1 (closure (interior (closure (interior A)))))

theorem Topology.P3_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) :
    Topology.P3 (A ∪ B ∪ C) := by
  -- First, obtain `P3` for `A ∪ B`.
  have hAB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P3 ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left-associative) form.
  simpa [Set.union_assoc] using hABC

theorem Topology.closureInterior_sInter_subset
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    closure (interior (⋂₀ 𝒜 : Set X)) ⊆
      ⋂₀ ((fun S : Set X => closure (interior S)) '' 𝒜) := by
  intro x hx
  -- To show `x` lies in the big intersection, we prove it belongs to each
  -- member of the image of `𝒜` under `closure ∘ interior`.
  apply Set.mem_sInter.2
  intro S hS
  -- Destructure `hS` to obtain the originating set `T ∈ 𝒜` with `S = closure (interior T)`.
  rcases hS with ⟨T, hT𝒜, rfl⟩
  -- We have to prove `x ∈ closure (interior T)`.
  -- First, note `⋂₀ 𝒜 ⊆ T`.
  have h_incl : (⋂₀ 𝒜 : Set X) ⊆ T := by
    intro y hy
    exact (Set.mem_sInter.1 hy) T hT𝒜
  -- Hence `interior (⋂₀ 𝒜) ⊆ interior T` by monotonicity of `interior`.
  have h_int : interior (⋂₀ 𝒜 : Set X) ⊆ interior T :=
    interior_mono h_incl
  -- Taking closures preserves inclusions, yielding the desired containment.
  have h_closure : closure (interior (⋂₀ 𝒜 : Set X)) ⊆ closure (interior T) :=
    closure_mono h_int
  -- Apply this inclusion to `x`.
  exact h_closure hx

theorem Topology.interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- For each `i`, show `x ∈ interior (A i)`.
  have h_each : ∀ i, (x : X) ∈ interior (A i) := by
    intro i
    -- The intersection is contained in `A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `interior` gives the desired inclusion.
    have h_int_mono : interior (⋂ j, A j) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_int_mono hx
  -- Combine the pointwise facts into the intersection.
  exact Set.mem_iInter.2 h_each

theorem Topology.interiorClosureInteriorClosure_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) ⊆ interior (closure A) := by
  simpa [closure_closure] using
    (Topology.interiorClosureInterior_subset_interiorClosure
      (X := X) (A := closure A))

theorem Topology.interior_inter_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  -- First inclusion: `interior (A ∩ B) ⊆ interior A ∩ B`.
  have h₁ : interior (A ∩ B : Set X) ⊆ interior A ∩ B := by
    have h := Topology.interior_inter_subset (X := X) (A := A) (B := B)
    simpa [hB.interior_eq] using h
  -- Second inclusion: `interior A ∩ B ⊆ interior (A ∩ B)`.
  have h₂ : interior A ∩ B ⊆ interior (A ∩ B) := by
    intro x hx
    rcases hx with ⟨hx_intA, hxB⟩
    -- The set `interior A ∩ B` is open and contains `x`.
    have h_open : IsOpen (interior A ∩ B) :=
      IsOpen.inter isOpen_interior hB
    -- This set is contained in `A ∩ B`.
    have h_subset : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy; exact ⟨interior_subset hy.1, hy.2⟩
    -- Hence it lies in the interior of `A ∩ B`.
    have h_max : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal h_subset h_open
    exact h_max ⟨hx_intA, hxB⟩
  -- Combine the inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.Subset_interiorClosure_of_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hB : Topology.P3 B) :
    (A : Set X) ⊆ interior (closure B) := by
  intro x hxA
  have hxB : (x : X) ∈ B := hAB hxA
  exact hB hxB

theorem Topology.interior_inter_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  -- First inclusion: `interior (A ∩ B) ⊆ A ∩ interior B`.
  have h₁ : interior (A ∩ B : Set X) ⊆ A ∩ interior B := by
    -- Use the general inclusion and rewrite `interior A` using openness.
    have h := Topology.interior_inter_subset (X := X) (A := A) (B := B)
    simpa [hA.interior_eq] using h
  -- Second inclusion: `A ∩ interior B ⊆ interior (A ∩ B)`.
  have h₂ : A ∩ interior B ⊆ interior (A ∩ B) := by
    intro x hx
    rcases hx with ⟨hxA, hx_intB⟩
    -- The set `A ∩ interior B` is an open neighbourhood of `x`.
    have h_open : IsOpen (A ∩ interior B) :=
      IsOpen.inter hA isOpen_interior
    -- It is contained in `A ∩ B`.
    have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨hy.1, interior_subset hy.2⟩
    -- Hence it lies inside the interior of `A ∩ B`.
    have h_max :
        (A ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal h_subset h_open
    exact h_max ⟨hxA, hx_intB⟩
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.P2_iff_P3_of_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.P2_iff_P3_of_isOpen (X := X) (A := interior A) h_open)

theorem Topology.closureInteriorClosure_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure A := by
  intro hP2
  -- From `P2` we immediately obtain `P3`.
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- The desired equality follows from the corresponding lemma for `P3`.
  exact
    Topology.closureInteriorClosure_eq_closure_of_P3
      (X := X) (A := A) hP3

theorem Topology.closure_eq_univ_iff_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro h_closure
    -- Rewrite using `h_closure` and `interior_univ`.
    have : interior (closure (A : Set X)) = interior (Set.univ : Set X) := by
      simpa [h_closure]
    simpa [interior_univ] using this
  · intro h_int
    -- From `interior (closure A) = univ` we get `univ ⊆ closure A`.
    have h_subset₁ : (Set.univ : Set X) ⊆ closure A := by
      have : interior (closure A) ⊆ closure A := interior_subset
      simpa [h_int] using this
    -- The opposite inclusion is trivial.
    have h_subset₂ : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx; simp
    exact Set.Subset.antisymm h_subset₂ h_subset₁

theorem Topology.P2_closureInterior_iff_P3_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ :=
    Topology.P2_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  have h₂ :=
    Topology.P3_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  simpa using h₁.trans h₂.symm

theorem Topology.closure_has_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 (closure A) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have h_closureInt : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Hence `closure A` is also the whole space.
  have h_closureA_univ : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`.
    have h_sub : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- Using `h_closureInt`, this means `univ ⊆ closure A`.
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_closureInt] using h_sub
    -- The reverse inclusion is trivial.
    have h_superset : closure A ⊆ (Set.univ : Set X) := by
      intro x hx; simp
    exact Set.Subset.antisymm h_superset h_subset
  -- Since `closure A = univ`, it is open, so it satisfies `P3`.
  have h_open : IsOpen (closure A) := by
    simpa [h_closureA_univ] using (isOpen_univ : IsOpen (Set.univ : Set X))
  exact Topology.isOpen_implies_P3 (X := X) (A := closure A) h_open

theorem Topology.interiorClosure_iterate_idempotent₂
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- First reduction using idempotence on `interior (closure (interior A))`.
  have h1 :
      interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
    simpa using
      (Topology.interiorClosure_idempotent
        (X := X) (A := interior (closure (interior A))))
  -- Second reduction using idempotence on `interior A`.
  have h2 :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) := by
    simpa using
      (Topology.interiorClosure_idempotent
        (X := X) (A := interior A))
  -- Combine the two equalities.
  simpa using (h1.trans h2)

theorem Topology.dense_iff_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (Aᶜ : Set X) = (∅ : Set X) := by
  classical
  -- Density is equivalent to `closure A = univ`.
  have h_dense :
      Dense (A : Set X) ↔ closure (A : Set X) = (Set.univ : Set X) :=
    dense_iff_closure_eq (s := (A : Set X))
  -- `interior (Aᶜ)` is the complement of `closure A`.
  have h_int_compl : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := by
    simpa using interior_compl
  -- Relate `closure A = univ` to `interior (Aᶜ) = ∅`.
  have h_aux :
      closure (A : Set X) = (Set.univ : Set X) ↔
        interior (Aᶜ : Set X) = (∅ : Set X) := by
    constructor
    · intro h_cl
      have : interior (Aᶜ : Set X) = (Set.univ : Set X)ᶜ := by
        simpa [h_cl] using h_int_compl
      simpa [Set.compl_univ] using this
    · intro h_int
      -- From `h_int_compl`, the complement of the closure is empty.
      have h_compl : (closure (A : Set X))ᶜ = (∅ : Set X) := by
        have : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := h_int_compl
        simpa [this] using h_int
      -- Therefore `closure A` is the whole space.
      have : closure (A : Set X) = ((closure (A : Set X))ᶜ)ᶜ := by
        simp
      simpa [h_compl, Set.compl_empty] using this
  simpa using h_dense.trans h_aux

theorem Topology.eq_univ_of_isClosed_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (interior A)) :
    (A : Set X) = (Set.univ : Set X) := by
  -- From density we know that the closure of `interior A` is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Since `A` is closed and contains `interior A`, it contains the closure of `interior A`.
  have h_subset : closure (interior A) ⊆ A :=
    closure_minimal (interior_subset : interior A ⊆ A) hA_closed
  -- Therefore `univ ⊆ A`.
  have h_univ_subset : (Set.univ : Set X) ⊆ A := by
    simpa [h_closure] using h_subset
  -- The reverse inclusion is trivial.
  have h_subset_univ : (A : Set X) ⊆ Set.univ := by
    intro _ _; simp
  exact Set.Subset.antisymm h_subset_univ h_univ_subset

theorem Topology.closureInteriorClosure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- From `A ⊆ B`, we get `closure A ⊆ closure B`.
  have h₁ : (closure A : Set X) ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves the inclusion.
  have h₂ : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Taking closures once more yields the desired inclusion.
  exact closure_mono h₂

theorem Topology.P2_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      IsOpen (closure (interior (closure A))) := by
  -- `closure (interior (closure A))` is a closed set.
  have h_closed : IsClosed (closure (interior (closure A))) := isClosed_closure
  -- Apply the general equivalence between `P2` and openness for closed sets.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (closure A))) h_closed)

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  exact (Topology.univ_satisfies_P1_P2_P3 (X := X)).2.2

theorem Topology.interior_inter_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B : Set X) = A ∩ B := by
  simpa using (IsOpen.inter hA hB).interior_eq

theorem Topology.interior_union_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B : Set X) := IsOpen.union hA hB
  simpa using hOpen.interior_eq

theorem Topology.isOpen_closure_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure A) := by
  intro hDense
  -- From the density of `interior A`, we know `closure A` satisfies `P3`.
  have hP3 : Topology.P3 (closure A) :=
    Topology.closure_has_P3_of_denseInterior (X := X) (A := A) hDense
  -- For closed sets, `P3` is equivalent to being open.
  exact
    ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1) hP3

theorem Topology.interior_eq_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  -- From `P3` and closedness, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hP3
  -- For an open set, the interior equals the set itself.
  simpa using hOpen.interior_eq

theorem Topology.P2_of_closureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 A := by
  intro hEq
  have hDense : Dense (interior A) :=
    (dense_iff_closure_eq (s := (interior A : Set X))).2 hEq
  exact Topology.P2_of_denseInterior (X := X) (A := A) hDense

theorem Topology.Subset_interiorClosureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hB : Topology.P2 B) :
    (A : Set X) ⊆ interior (closure (interior B)) := by
  dsimp [Topology.P2] at hB
  intro x hxA
  have hxB : (x : X) ∈ B := hAB hxA
  exact hB hxB

theorem Topology.closureInterior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h_subset : (interior A : Set X) ⊆ A := interior_subset
  exact closure_minimal h_subset hA_closed

theorem Topology.closureInteriorClosure_isClosed
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (closure A))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (closure A))))

theorem Topology.closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure ((⋂ i, A i) : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each index `i`, we show that `x ∈ closure (A i)`.
  have h_each : ∀ i, (x : X) ∈ closure (A i) := by
    intro i
    -- Since `⋂ i, A i ⊆ A i`, taking closures preserves the inclusion.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_closure_subset :
        closure ((⋂ j, A j) : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure_subset hx
  exact Set.mem_iInter.2 h_each

theorem Topology.closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Show `x ∈ closure A`.
  have hxA : (x : X) ∈ closure A := by
    -- `A ∩ B ⊆ A`
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    -- Taking closures preserves the inclusion.
    have h_closure : closure (A ∩ B : Set X) ⊆ closure A :=
      closure_mono h_subset
    exact h_closure hx
  -- Show `x ∈ closure B`.
  have hxB : (x : X) ∈ closure B := by
    -- `A ∩ B ⊆ B`
    have h_subset : (A ∩ B : Set X) ⊆ B := by
      intro y hy; exact hy.2
    -- Taking closures preserves the inclusion.
    have h_closure : closure (A ∩ B : Set X) ⊆ closure B :=
      closure_mono h_subset
    exact h_closure hx
  exact And.intro hxA hxB

theorem Topology.P3_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    Topology.P3 (⋃ i, A i) := by
  -- Each open set `A i` satisfies `P3`.
  have hP3 : ∀ i, Topology.P3 (A i) := by
    intro i
    exact Topology.isOpen_implies_P3 (X := X) (A := A i) (hA i)
  -- Take the union over all indices.
  exact Topology.P3_iUnion (X := X) (A := A) hP3

theorem Topology.dense_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Dense (A : Set X)) (hB : Dense (B : Set X)) :
    Dense (A ∪ B : Set X) := by
  -- The closure of `A` is the whole space.
  have hA_closure : closure (A : Set X) = (Set.univ : Set X) := hA.closure_eq
  -- Since `A ⊆ A ∪ B`, we have `closure A ⊆ closure (A ∪ B)`.
  have h_superset : (Set.univ : Set X) ⊆ closure (A ∪ B : Set X) := by
    have h₁ : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have h_subset : (A : Set X) ⊆ A ∪ B := by
        intro x hx; exact Or.inl hx
      exact closure_mono h_subset
    simpa [hA_closure] using h₁
  -- The reverse inclusion is trivial.
  have h_subset : closure (A ∪ B : Set X) ⊆ (Set.univ : Set X) := by
    intro x _hx; simp
  -- Therefore the closure of `A ∪ B` is the whole space.
  have h_closure_union : closure (A ∪ B : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm h_subset h_superset
  -- Conclude that `A ∪ B` is dense.
  exact (dense_iff_closure_eq).2 h_closure_union

theorem Topology.P3_inter_three_of_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) (hC_closed : IsClosed C)
    (hA_P3 : Topology.P3 A) (hB_P3 : Topology.P3 B) (hC_P3 : Topology.P3 C) :
    Topology.P3 (A ∩ B ∩ C) := by
  -- From `P3` and closedness we deduce that `A`, `B`, and `C` are open.
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1 hA_P3
  have hB_open : IsOpen B :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB_closed).1 hB_P3
  have hC_open : IsOpen C :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := C) hC_closed).1 hC_P3
  -- The intersection of finitely many open sets is open.
  have hABC_open : IsOpen (A ∩ B ∩ C) := by
    have hAB_open : IsOpen (A ∩ B) := IsOpen.inter hA_open hB_open
    simpa [Set.inter_assoc] using IsOpen.inter hAB_open hC_open
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A ∩ B ∩ C) hABC_open

theorem Topology.P1_iff_P3_of_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  -- `interior A` is an open set.
  have hOpen : IsOpen (interior A) := isOpen_interior
  -- Apply the existing equivalence for open sets.
  simpa using
    (Topology.P1_iff_P3_of_isOpen (X := X) (A := interior A) hOpen)

theorem Topology.Subset_closureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 A) :
    (A : Set X) ⊆ closure (interior A) := by
  dsimp [Topology.P2] at hA
  intro x hx
  have hx_int : (x : X) ∈ interior (closure (interior A)) := hA hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int

theorem Topology.P1_iff_P2_of_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := interior A) hOpen)

theorem Topology.interior_closure_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B : Set X)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]

theorem Topology.dense_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (A : Set X) := by
  intro hDenseInt
  -- The closure of `interior A` is the whole space.
  have hInt : closure (interior A) = (Set.univ : Set X) := hDenseInt.closure_eq
  -- `closure (interior A)` is contained in `closure A`.
  have hSub : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Hence `closure A` contains the whole space.
  have hUnivSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    simpa [hInt] using hSub
  -- The opposite inclusion is trivial, so `closure A = univ`.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    · exact hUnivSub
  -- Conclude that `A` is dense.
  exact (dense_iff_closure_eq).2 hClosureA

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  exact (Topology.univ_satisfies_P1_P2_P3 (X := X)).2.1

theorem Topology.P2_inter_three_of_closed
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) (hC_closed : IsClosed C)
    (hA_P2 : Topology.P2 A) (hB_P2 : Topology.P2 B) (hC_P2 : Topology.P2 C) :
    Topology.P2 (A ∩ B ∩ C) := by
  -- First, obtain `P2` for the intersection `A ∩ B`.
  have hAB_P2 : Topology.P2 (A ∩ B) :=
    Topology.P2_inter_of_closed (X := X) (A := A) (B := B)
      hA_closed hB_closed hA_P2 hB_P2
  -- `A ∩ B` is closed, being the intersection of two closed sets.
  have hAB_closed : IsClosed (A ∩ B) := IsClosed.inter hA_closed hB_closed
  -- Intersect the result with `C`, using the two–set lemma once more.
  have hABC_P2 : Topology.P2 ((A ∩ B) ∩ C) :=
    Topology.P2_inter_of_closed (X := X) (A := A ∩ B) (B := C)
      hAB_closed hC_closed hAB_P2 hC_P2
  -- Rewrite the associative intersection to match the desired statement.
  simpa [Set.inter_assoc] using hABC_P2

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  exact (Topology.univ_satisfies_P1_P2_P3 (X := X)).1

theorem Topology.P2_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure (closure (A : Set X))) ↔ Topology.P2 (closure A) := by
  simpa [closure_closure]

theorem Topology.P2_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) : Topology.P2 (⋃ i, A i) := by
  -- Each open set `A i` satisfies `P2`.
  have hA_P2 : ∀ i, Topology.P2 (A i) := by
    intro i
    exact Topology.isOpen_implies_P2 (X := X) (A := A i) (hA i)
  -- Apply the existing union lemma for `P2`.
  exact Topology.P2_iUnion (X := X) (A := A) hA_P2

theorem Topology.closureInterior_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.P3_closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (closure (A : Set X))) ↔ Topology.P3 (closure A) := by
  simpa [closure_closure]

theorem Topology.dense_of_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) → Dense (A : Set X) := by
  intro h
  exact ((dense_iff_closure_eq (s := (A : Set X))).2 h)

theorem Topology.iUnion_closure_subset_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (A i)` is contained in `closure (⋃ i, A i)` by monotonicity.
  have h_closure_mono :
      closure (A i : Set X) ⊆ closure (⋃ j, A j) := by
    -- First, note `A i ⊆ ⋃ j, A j`.
    have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    -- Taking closures preserves inclusions.
    exact closure_mono h_subset
  exact h_closure_mono hx_i

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
  -- `A i` is contained in `⋃ j, A j`
  have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Monotonicity of `interior` yields the desired inclusion.
  have h_mono : interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono h_subset
  exact h_mono hx_int

theorem Topology.closure_satisfies_P1_P2_P3_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (A : Set X)) :
    Topology.P1 (closure (A : Set X)) ∧
      Topology.P2 (closure (A : Set X)) ∧
      Topology.P3 (closure (A : Set X)) := by
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    Topology.closure_has_P1_of_dense (X := X) (A := A) hDense
  have hP2 : Topology.P2 (closure (A : Set X)) :=
    Topology.P2_closure_of_dense (X := X) (A := A) hDense
  have hP3 : Topology.P3 (closure (A : Set X)) :=
    Topology.P3_closure_of_dense (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.closure_iUnion_interior_subset_closureInterior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋃ i, interior (A i) : Set X) ⊆
      closure (interior (⋃ i, A i)) := by
  -- First, prove the set inside the left‐hand closure is contained in the right‐hand interior.
  have h_subset : (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
    -- `A i` is contained in the union, hence its interior is contained in the interior of the union.
    have h_int_mono :
        interior (A i : Set X) ⊆ interior (⋃ j, A j) := by
      have h_subset' : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset'
    exact h_int_mono hx_int
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono h_subset

theorem Topology.P2_closureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure (interior (closure (interior A)))) ↔
      Topology.P2 (closure (interior A)) := by
  have hEq :
      (closure (interior (closure (interior A))) : Set X) =
        closure (interior A) :=
    Topology.closureInterior_idempotent (X := X) (A := A)
  simpa [hEq] using
    (Iff.rfl :
      Topology.P2 (closure (interior (closure (interior A)))) ↔
        Topology.P2 (closure (interior (closure (interior A)))))

theorem Topology.P2_closure_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ interior (closure A) = closure A := by
  -- `closure A` is a closed set.
  have hClosed : IsClosed (closure A) := isClosed_closure
  -- For a closed set, `P2` is equivalent to being open.
  have h₁ :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure A) hClosed)
  -- An open set is characterised by the equality with its interior.
  have h₂ : IsOpen (closure A) ↔ interior (closure A) = closure A := by
    constructor
    · intro hOpen
      simpa [hOpen.interior_eq]
    · intro hEq
      -- Since `interior (closure A)` is open, the equality implies
      -- `closure A` is open as well.
      have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂

theorem Topology.closure_has_P2_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure A) := by
  intro hDense
  -- From the density of `interior A`, we know `closure A` satisfies `P3`.
  have hP3 : Topology.P3 (closure A) :=
    Topology.closure_has_P3_of_denseInterior (X := X) (A := A) hDense
  -- A `P3` closure yields `P2` for the same closure.
  exact Topology.P2_of_P3_closure (X := X) (A := A) hP3

theorem Topology.P3_interiorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (closure (interior (closure A)))) ↔
      Topology.P3 (interior (closure A)) := by
  have hEq :
      (interior (closure (interior (closure A))) : Set X) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (X := X) (A := A)
  simpa [hEq] using
    (Iff.rfl :
      Topology.P3 (interior (closure (interior (closure A)))) ↔
        Topology.P3 (interior (closure (interior (closure A)))))

theorem Topology.isOpen_closureInterior_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → IsOpen (closure (interior A)) := by
  intro hDense
  have h_eq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem Topology.dense_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Dense (closure (A : Set X)) := by
  intro hDense
  have h_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  have h_closure_eq : closure (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [closure_closure, h_eq, closure_univ]
  exact (dense_iff_closure_eq).2 h_closure_eq

theorem Topology.closureInterior_eq_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure (interior (closure A)) = closure A := by
  intro hP3
  simpa using
    (Topology.closureInteriorClosure_eq_closure_of_P3 (X := X) (A := A) hP3)

theorem Topology.isOpen_inter_three_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∩ B ∩ C) ∧ Topology.P2 (A ∩ B ∩ C) ∧ Topology.P3 (A ∩ B ∩ C) := by
  -- The intersection of three open sets is open.
  have hOpen : IsOpen (A ∩ B ∩ C) := by
    have hAB : IsOpen (A ∩ B) := IsOpen.inter hA hB
    have hABC : IsOpen ((A ∩ B) ∩ C) := IsOpen.inter hAB hC
    simpa [Set.inter_assoc] using hABC
  -- Any open set satisfies `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := A ∩ B ∩ C) hOpen

theorem Topology.P1_closure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (closure (A : Set X))) ↔ Topology.P1 (closure A) := by
  simpa [closure_closure]

theorem Topology.P2_and_P3_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    Topology.P2 (closure A) ∧ Topology.P3 (closure A) := by
  have hP2 : Topology.P2 (closure A) :=
    (Topology.P2_of_isOpen_closure (X := X) (A := A)) h_open
  have hP3 : Topology.P3 (closure A) :=
    ((Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).2) h_open
  exact ⟨hP2, hP3⟩

theorem Topology.interior_sInter_subset
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    interior (⋂₀ 𝒜 : Set X) ⊆ ⋂₀ ((fun S : Set X => interior S) '' 𝒜) := by
  intro x hx
  -- For each `S ∈ 𝒜`, we have `x ∈ interior S`.
  have h₁ : ∀ S : Set X, S ∈ 𝒜 → (x : X) ∈ interior S := by
    intro S hS
    have h_subset : (⋂₀ 𝒜 : Set X) ⊆ S := by
      intro y hy
      exact (Set.mem_sInter.1 hy) S hS
    have h_int_mono :
        interior (⋂₀ 𝒜 : Set X) ⊆ interior S :=
      interior_mono h_subset
    exact h_int_mono hx
  -- Show that `x` lies in every element of the image `interior '' 𝒜`.
  have : ∀ T : Set X,
      T ∈ ((fun S : Set X => interior S) '' 𝒜) → (x : X) ∈ T := by
    intro T hT
    rcases hT with ⟨S, hS𝒜, rfl⟩
    exact h₁ S hS𝒜
  exact (Set.mem_sInter.2 this)

theorem Topology.Subset_closureInteriorClosure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure A)) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  have h_step :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closureInterior_subset_closureInteriorClosure (X := X) (A := A)
  exact Set.Subset.trans hP1 h_step

theorem Topology.closure_sInter_subset
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    closure (⋂₀ 𝒜 : Set X) ⊆ ⋂₀ ((fun S : Set X => closure S) '' 𝒜) := by
  intro x hx
  apply Set.mem_sInter.2
  intro S hS
  rcases hS with ⟨T, hT𝒜, rfl⟩
  -- Since `⋂₀ 𝒜 ⊆ T`, taking closures preserves the inclusion.
  have h_subset : (⋂₀ 𝒜 : Set X) ⊆ T := by
    intro y hy
    exact (Set.mem_sInter.1 hy) T hT𝒜
  have h_closure_subset :
      closure (⋂₀ 𝒜 : Set X) ⊆ closure T := closure_mono h_subset
  exact h_closure_subset hx

theorem Topology.interior_diff_eq_closure_compl
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior (A \ B : Set X) = A \ closure B := by
  classical
  -- First, show `interior (A \ B) ⊆ A \ closure B`.
  have h₁ : interior (A \ B : Set X) ⊆ A \ closure B := by
    intro x hx_int
    -- `x ∈ A \ B`
    have hx_mem : (x : X) ∈ A \ B :=
      (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hx_int
    rcases hx_mem with ⟨hxA, hxNotB⟩
    -- Show `x ∉ closure B`
    have hNotClB : (x : X) ∉ closure B := by
      by_contra h_cl
      -- Every neighbourhood of `x` meets `B`, so in particular `interior (A \ B)` does.
      have h_nonempty :
          ((interior (A \ B) : Set X) ∩ B).Nonempty :=
        ((mem_closure_iff).1 h_cl) (interior (A \ B)) isOpen_interior hx_int
      rcases h_nonempty with ⟨y, hyInt, hyB⟩
      -- But `interior (A \ B)` is disjoint from `B`.
      have : (y : X) ∈ A \ B :=
        (interior_subset : interior (A \ B) ⊆ A \ B) hyInt
      exact this.2 hyB
    exact And.intro hxA hNotClB
  -- Second, show `A \ closure B ⊆ interior (A \ B)`.
  have h₂ : A \ closure B ⊆ interior (A \ B : Set X) := by
    intro x hx
    rcases hx with ⟨hxA, hxNotClB⟩
    -- The set `U = A ∩ (closure B)ᶜ` is an open neighbourhood of `x`
    -- contained in `A \ B`.
    let U : Set X := A ∩ (closure B)ᶜ
    have hU_open : IsOpen U :=
      IsOpen.inter hA isClosed_closure.isOpen_compl
    have hxU : (x : X) ∈ U := by
      have : (x : X) ∈ (closure B)ᶜ := hxNotClB
      simpa [U] using And.intro hxA this
    have hU_subset : (U : Set X) ⊆ A \ B := by
      intro y hy
      rcases hy with ⟨hyA, hyNotClB⟩
      have hyNotB : (y : X) ∉ B := by
        intro hyB
        have : (y : X) ∈ closure B := subset_closure hyB
        exact hyNotClB this
      exact And.intro hyA hyNotB
    -- Since `U` is open and contained in `A \ B`, it lies in the interior.
    have hU_interior : (U : Set X) ⊆ interior (A \ B : Set X) :=
      interior_maximal hU_subset hU_open
    exact hU_interior hxU
  -- Combine both inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.closure_interiorUnion_subset_closureInterior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior A) ∪ (interior B) : Set X) ⊆
      closure (interior (A ∪ B)) := by
  have h_sub :
      ((interior A) ∪ (interior B) : Set X) ⊆ interior (A ∪ B) :=
    Topology.union_interior_subset_interior_union'
      (X := X) (A := A) (B := B)
  exact closure_mono h_sub

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  simpa using
    (Topology.empty_satisfies_P1_P2_P3 (X := X)).2.2

theorem Topology.dense_iff_closureInteriorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- Since `A` is dense, its closure is the whole space.
    have h_closureA : closure (A : Set X) = (Set.univ : Set X) :=
      hDense.closure_eq
    -- Hence the interior of this closure is also the whole space.
    have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
      simpa [h_closureA] using
        (interior_univ : interior (Set.univ : Set X) = Set.univ)
    -- Taking the closure again yields the desired equality.
    simpa [h_int, closure_univ]
  · intro hEq
    -- The given equality implies that `interior (closure A)` is dense.
    have hDenseInt :
        Dense (interior (closure (A : Set X))) := by
      have : closure (interior (closure (A : Set X))) = (Set.univ : Set X) := hEq
      exact
        ((dense_iff_closure_eq
            (s := (interior (closure (A : Set X)) : Set X))).2) this
    -- Density of `interior (closure A)` implies density of `A`.
    exact
      Topology.dense_of_denseInteriorClosure
        (X := X) (A := A) hDenseInt

theorem Topology.isOpen_union_three_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∪ B ∪ C) ∧ Topology.P2 (A ∪ B ∪ C) ∧ Topology.P3 (A ∪ B ∪ C) := by
  -- Establish that the union `A ∪ B ∪ C` is open.
  have hOpen : IsOpen (A ∪ B ∪ C) := by
    have hAB : IsOpen (A ∪ B) := IsOpen.union hA hB
    exact IsOpen.union hAB hC
  -- Invoke the generic result for open sets.
  simpa using
    Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A ∪ B ∪ C) hOpen

theorem Topology.closureInterior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem Topology.interiorClosureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Show `x ∈ interior (closure (interior A))`
  have hxA : (x : X) ∈ interior (closure (interior A)) := by
    -- `interior (A ∩ B) ⊆ interior A`
    have h_int_subset : interior (A ∩ B : Set X) ⊆ interior A :=
      interior_mono (by
        intro y hy
        exact hy.1)
    -- Hence `closure (interior (A ∩ B)) ⊆ closure (interior A)`
    have h_closure_subset :
        closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) :=
      closure_mono h_int_subset
    -- Taking interiors preserves the inclusion
    have h_interior_subset :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior A)) :=
      interior_mono h_closure_subset
    exact h_interior_subset hx
  -- Show `x ∈ interior (closure (interior B))`
  have hxB : (x : X) ∈ interior (closure (interior B)) := by
    -- `interior (A ∩ B) ⊆ interior B`
    have h_int_subset : interior (A ∩ B : Set X) ⊆ interior B :=
      interior_mono (by
        intro y hy
        exact hy.2)
    -- Hence `closure (interior (A ∩ B)) ⊆ closure (interior B)`
    have h_closure_subset :
        closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) :=
      closure_mono h_int_subset
    -- Taking interiors preserves the inclusion
    have h_interior_subset :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior B)) :=
      interior_mono h_closure_subset
    exact h_interior_subset hx
  exact And.intro hxA hxB

theorem Topology.closureInteriorClosure_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure A)) := by
  simpa [closure_closure]

theorem Topology.interior_inter_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A ∩ closure (A : Set X)) = interior (A : Set X) := by
  -- Since `A ⊆ closure A`, the intersection `A ∩ closure A` is just `A`.
  have h : (A ∩ closure (A : Set X) : Set X) = A := by
    have hsubset : (A : Set X) ⊆ closure A := subset_closure
    simpa [Set.inter_eq_left.2 hsubset]
  simpa [h]

theorem Topology.P3_closureInteriorClosure_iff_isOpen_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (interior (closure A))) ↔
      IsOpen (closure (interior (closure A))) := by
  -- `closure (interior (closure A))` is a closed set.
  have hClosed : IsClosed (closure (interior (closure A))) := isClosed_closure
  -- Apply the existing equivalence between `P3` and openness for closed sets.
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior (closure A))) hClosed)

theorem Topology.P3_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen S) :
    Topology.P3 (⋃₀ 𝒜) := by
  -- Each open set in `𝒜` satisfies `P3`.
  have hP3 : ∀ S : Set X, S ∈ 𝒜 → Topology.P3 S := by
    intro S hS
    exact Topology.isOpen_implies_P3 (X := X) (A := S) (h𝒜 S hS)
  -- Apply the union lemma for `P3`.
  exact Topology.P3_sUnion (X := X) (𝒜 := 𝒜) hP3

theorem Topology.P2_inter_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) : Topology.P2 (A ∩ B) := by
  simpa using
    (Topology.isOpen_inter_satisfies_P1_P2_P3 (X := X) (A := A) (B := B) hA hB).2.1

theorem Topology.closureInteriorClosure_union_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∪ B : Set X))) =
      closure (interior (closure A ∪ closure B)) := by
  simpa [closure_union]

theorem Topology.interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  -- The set `A \ B` is contained in `A`.
  exact interior_mono (by
    intro x hx
    exact hx.1)

theorem Topology.interior_union_three_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    interior (A ∪ B ∪ C : Set X) = A ∪ B ∪ C := by
  -- The union of three open sets is open.
  have hOpen : IsOpen (A ∪ B ∪ C : Set X) := by
    have hAB : IsOpen (A ∪ B : Set X) := IsOpen.union hA hB
    exact IsOpen.union hAB hC
  -- The interior of an open set is the set itself.
  simpa using hOpen.interior_eq

theorem Topology.closureInterior_eq_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = (A : Set X) := by
  have hEq : closure (interior A) = closure (A : Set X) :=
    Topology.closureInterior_eq_closure_of_P2 (X := X) (A := A) hP2
  simpa [hA_closed.closure_eq] using hEq

theorem Topology.interiorClosure_inter_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∩ B : Set X)) = interior (A ∩ B) := by
  -- Since `A ∩ B` is closed, its closure is itself.
  have hClosure : closure (A ∩ B : Set X) = A ∩ B :=
    (IsClosed.inter hA hB).closure_eq
  simpa [hClosure]

theorem Topology.interiorClosure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem Topology.P2_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen S) :
    Topology.P2 (⋃₀ 𝒜) := by
  -- Each open set in `𝒜` satisfies `P2`.
  have hP2 : ∀ S : Set X, S ∈ 𝒜 → Topology.P2 S := by
    intro S hS
    exact Topology.isOpen_implies_P2 (X := X) (A := S) (h𝒜 S hS)
  -- Apply the sUnion lemma for `P2`.
  exact Topology.P2_sUnion (X := X) (𝒜 := 𝒜) hP2

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  -- We reuse the existing result that the empty set satisfies all three properties.
  have h := Topology.empty_satisfies_P1_P2_P3 (X := X)
  exact h.2.1

theorem Topology.P2_inter_three_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P2 (A ∩ B ∩ C) := by
  -- Use the existing lemma that an intersection of three open sets satisfies
  -- all three `P` properties, then extract the `P2` component.
  have h :=
    Topology.isOpen_inter_three_satisfies_P1_P2_P3
      (X := X) (A := A) (B := B) (C := C) hA hB hC
  exact h.2.1

theorem Topology.isOpen_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → IsOpen (closure (A : Set X)) := by
  intro hDense
  have h_eq : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem Topology.P1_interiorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (interior (closure A)))) ↔
      Topology.P1 (interior (closure A)) := by
  have hEq :
      (interior (closure (interior (closure A))) : Set X) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (X := X) (A := A)
  simpa [hEq] using
    (Iff.rfl :
      Topology.P1 (interior (closure (interior (closure A)))) ↔
        Topology.P1 (interior (closure (interior (closure A)))))

theorem Topology.closure_inter_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B : Set X) = (A ∩ B : Set X) := by
  -- The intersection of two closed sets is itself closed.
  have hClosed : IsClosed (A ∩ B : Set X) := IsClosed.inter hA hB
  -- A closed set is equal to its closure.
  simpa using hClosed.closure_eq

theorem Topology.interior_inter_three_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∩ B ∩ C : Set X) = A ∩ B ∩ C := by
  have hOpen : IsOpen (A ∩ B ∩ C : Set X) := by
    -- `A ∩ B` is open since both `A` and `B` are open.
    have hAB : IsOpen (A ∩ B : Set X) := IsOpen.inter hA hB
    -- Intersect once more with `C`, which is also open.
    simpa [Set.inter_assoc] using IsOpen.inter hAB hC
  -- The interior of an open set coincides with the set itself.
  simpa using hOpen.interior_eq

theorem Topology.P2_iff_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First, for a closed set `A`, `P2 A` is equivalent to `IsOpen A`.
  have h₁ := Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  -- Next, an open set coincides with its interior, and conversely.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      -- Since `interior A` is open, the equality forces `A` to be open.
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem Topology.closureUnion_has_P1_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure (A ∪ B : Set X)) := by
  have h_union : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  simpa using
    Topology.closure_has_P1_of_P1 (X := X) (A := A ∪ B) h_union



theorem Topology.P1_iff_P2_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences already available for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP1
    -- Deduce `P2` from `P1`, then `P3` from `P2`.
    have hP2 : Topology.P2 A := (h₁).1 hP1
    have hP3 : Topology.P3 A := (h₂).1 hP2
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    -- From `P2` we recover `P1` using the first equivalence.
    exact (h₁).2 hP2

theorem Topology.closureInterior_eq_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    closure (interior A) = (A : Set X) := by
  -- From `P3` and closedness we have `interior A = A`.
  have h_int_eq : interior A = (A : Set X) :=
    Topology.interior_eq_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3
  -- Hence `closure (interior A) = closure A`.
  have h_cl_eq : closure (interior A) = closure (A : Set X) := by
    simpa [h_int_eq]
  -- Since `A` is closed, `closure A = A`.
  simpa [hA_closed.closure_eq] using h_cl_eq

theorem Topology.P3_of_isClosed_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (interior A)) :
    Topology.P3 A := by
  -- A closed set with dense interior is open (from the existing lemma).
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_denseInterior
      (X := X) (A := A) hA_closed hDense
  -- Every open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  simp

theorem Topology.interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  exact Set.Subset.trans (interior_subset : interior A ⊆ A)
    (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.interiorClosureInterior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`
      have h_mono :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- Step 1: `interior A ⊆ interior (A ∪ B)`
        have h_int_subset : interior A ⊆ interior (A ∪ B) := by
          have h_subset : (A : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inl hy
          exact interior_mono h_subset
        -- Step 2: take closures
        have h_closure_subset :
            closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        -- Step 3: take interiors again
        exact interior_mono h_closure_subset
      exact h_mono hxA
  | inr hxB =>
      -- The argument is symmetric for `B`.
      have h_mono :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- Step 1: `interior B ⊆ interior (A ∪ B)`
        have h_int_subset : interior B ⊆ interior (A ∪ B) := by
          have h_subset : (B : Set X) ⊆ A ∪ B := by
            intro y hy; exact Or.inr hy
          exact interior_mono h_subset
        -- Step 2: take closures
        have h_closure_subset :
            closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int_subset
        -- Step 3: take interiors again
        exact interior_mono h_closure_subset
      exact h_mono hxB

theorem Topology.closureInterior_eq_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen A) (hA_closed : IsClosed A) :
    closure (interior A) = (A : Set X) := by
  calc
    closure (interior A) = closure A := by
      simpa [hA_open.interior_eq]
    _ = A := by
      simpa [hA_closed.closure_eq]

theorem Topology.closure_subset_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B) := by
  have h_subset : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  exact closure_mono h_subset

theorem Topology.isOpen_closure_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure (A : Set X)) = closure A := by
  constructor
  · intro hOpen
    simpa [hOpen.interior_eq]
  · intro hEq
    have hOpenInt : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using hOpenInt



theorem Topology.clopen_closure_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) →
      IsOpen (closure (A : Set X)) ∧ IsClosed (closure (A : Set X)) := by
  intro hDense
  have hOpen : IsOpen (closure (A : Set X)) :=
    Topology.isOpen_closure_of_dense (X := X) (A := A) hDense
  exact ⟨hOpen, isClosed_closure⟩

theorem Topology.closureInterior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- `interior (A \ B)` is contained in `interior A`.
  have h_sub :
      (interior (A \ B : Set X) : Set X) ⊆ interior A :=
    Topology.interior_diff_subset (X := X) (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h_sub

theorem Topology.closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A := by
  -- The set `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_subset

theorem Topology.interior_iUnion_eq_iUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  have hOpen : IsOpen (⋃ i, A i : Set X) := isOpen_iUnion hA
  simpa using hOpen.interior_eq

theorem Topology.P3_closure_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔
      interior (closure (A : Set X)) = closure A := by
  have h₁ :=
    Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  have h₂ :=
    Topology.isOpen_closure_iff_interior_eq_closure (X := X) (A := A)
  simpa using h₁.trans h₂

theorem Topology.P3_of_interiorClosure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) → Topology.P3 A := by
  intro hIntUniv
  -- From `interior (closure A) = univ` we deduce `closure A = univ`.
  have hClosureUniv : closure (A : Set X) = (Set.univ : Set X) := by
    -- `interior (closure A)` is contained in `closure A`.
    have hSubset : (Set.univ : Set X) ⊆ closure A := by
      have hIntSubset : interior (closure (A : Set X)) ⊆ closure A :=
        interior_subset
      simpa [hIntUniv] using hIntSubset
    -- The reverse inclusion is trivial.
    have hSuperset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x _; simp
    exact Set.Subset.antisymm hSuperset hSubset
  -- Since `closure A = univ`, it is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    simpa [hClosureUniv] using (isOpen_univ : IsOpen (Set.univ : Set X))
  -- Apply the existing lemma to obtain `P3 A`.
  exact
    Topology.P3_of_isOpen_closure (X := X) (A := A) hOpen

theorem Topology.P3_implies_P1_and_P2_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P1 A ∧ Topology.P2 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3
  have hP2 : Topology.P2 A :=
    Topology.P2_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3
  exact And.intro hP1 hP2

theorem Topology.isOpen_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) : IsOpen A := by
  -- From density and closedness we get `A = univ`.
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    ((Topology.dense_iff_eq_univ_of_isClosed (X := X) (A := A) hA_closed).1)
      hDense
  -- The universe is open.
  simpa [h_eq] using (isOpen_univ : IsOpen (Set.univ : Set X))

theorem Topology.P1_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P1 A := by
  -- Since `A` is dense, its closure is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- But `A` is closed, so `closure A = A`, hence `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    simpa [hA_closed.closure_eq] using h_closure
  -- The universe satisfies `P1`, and rewriting via `hA_univ` concludes the proof.
  simpa [hA_univ] using (Topology.P1_univ (X := X))

theorem Topology.P1_and_P3_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    Topology.P1 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  have hP3 : Topology.P3 A :=
    Topology.P3_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  exact And.intro hP1 hP3

theorem Topology.dense_closure_iff_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure (A : Set X)) ↔ Dense (A : Set X) := by
  -- Rewrite both `Dense` predicates in terms of closures being the whole space.
  have h₁ :
      Dense (closure (A : Set X)) ↔
        closure (closure (A : Set X)) = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := (closure (A : Set X))))
  have h₂ :
      Dense (A : Set X) ↔
        closure (A : Set X) = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := (A : Set X)))
  -- Since `closure (closure A)` coincides with `closure A`, these conditions are equivalent.
  have h_eq :
      (closure (closure (A : Set X)) = (Set.univ : Set X)) ↔
        closure (A : Set X) = (Set.univ : Set X) := by
    simpa [closure_closure]
  -- Chain the equivalences to obtain the desired result.
  simpa using h₁.trans (h_eq.trans h₂.symm)

theorem Topology.closure_eq_univ_iff_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (Aᶜ : Set X) = (∅ : Set X) := by
  -- `closure A = univ` is equivalent to `Dense A`.
  have h₁ :
      closure (A : Set X) = (Set.univ : Set X) ↔ Dense (A : Set X) :=
    (dense_iff_closure_eq (s := (A : Set X))).symm
  -- `Dense A` is equivalent to `interior (Aᶜ) = ∅`.
  have h₂ :
      Dense (A : Set X) ↔ interior (Aᶜ : Set X) = (∅ : Set X) :=
    Topology.dense_iff_interior_compl_eq_empty (X := X) (A := A)
  -- Combine the two equivalences.
  simpa using h₁.trans h₂

theorem Topology.P1_P2_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) →
      Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hDense
  have hP1 := Topology.P1_of_denseInterior (X := X) (A := A) hDense
  have hP2 := Topology.P2_of_denseInterior (X := X) (A := A) hDense
  have hP3 := Topology.P3_of_denseInterior (X := X) (A := A) hDense
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.P2_closureInteriorClosure_iff_P3_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior (closure (A : Set X)))) ↔
      Topology.P3 (closure (interior (closure A))) := by
  -- Both properties are equivalent to the set being open.
  have h₁ :=
    Topology.P2_closureInteriorClosure_iff_isOpen_closureInteriorClosure
      (X := X) (A := A)
  have h₂ :=
    Topology.P3_closureInteriorClosure_iff_isOpen_closureInteriorClosure
      (X := X) (A := A)
  -- Chain the equivalences.
  exact h₁.trans h₂.symm

theorem Topology.dense_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Dense (A : Set X)) (hB : Dense (B : Set X)) (hC : Dense (C : Set X)) :
    Dense (A ∪ B ∪ C : Set X) := by
  -- First, the union `A ∪ B` is dense.
  have hAB : Dense (A ∪ B : Set X) :=
    Topology.dense_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Dense ((A ∪ B) ∪ C : Set X) :=
    Topology.dense_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left‐associative) form.
  simpa [Set.union_assoc] using hABC

theorem Topology.closureInterior_inter_eq_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A ∩ B : Set X)) = closure (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B : Set X) := IsOpen.inter hA hB
  simpa [hOpen.interior_eq]

theorem Topology.P1_inter_three_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P1 (A ∩ B ∩ C) := by
  exact
    (Topology.isOpen_inter_three_satisfies_P1_P2_P3
      (X := X) (A := A) (B := B) (C := C) hA hB hC).1

theorem Topology.interiorClosure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure A) := by
  -- `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves the inclusion.
  have h_closure_subset :
      closure (A \ B : Set X) ⊆ closure A := closure_mono h_subset
  -- Monotonicity of `interior` then yields the desired inclusion.
  exact interior_mono h_closure_subset

theorem Topology.closure_subset_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (B : Set X) ⊆ closure (A ∪ B) := by
  have h_subset : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  exact closure_mono h_subset

theorem Topology.isOpen_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsOpen (interior (closure (A : Set X))) := by
  exact isOpen_interior

theorem Topology.closure_union_eq_of_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    closure (A ∪ B : Set X) = (A ∪ B : Set X) := by
  have hClosed : IsClosed (A ∪ B : Set X) := IsClosed.union hA_closed hB_closed
  simpa using hClosed.closure_eq

theorem Topology.P2_iff_P1_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Existing equivalences for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Prove each implication separately.
  constructor
  · intro hP2
    have hP1 : Topology.P1 A := (h₁).mpr hP2
    have hP3 : Topology.P3 A := (h₂).1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _hP3⟩
    exact (h₁).1 hP1

theorem Topology.union_interior_three_subset_interior_union
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    (interior A ∪ interior B ∪ interior C : Set X) ⊆
      interior (A ∪ B ∪ C) := by
  -- We first handle the two–set case `A ∪ B`.
  have h₁ :
      (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) :=
    Topology.union_interior_subset_interior_union'
      (X := X) (A := A) (B := B)
  -- Next, we enlarge to include `C`.
  have h₂ :
      (interior (A ∪ B) ∪ interior C : Set X) ⊆
        interior ((A ∪ B) ∪ C) :=
    Topology.union_interior_subset_interior_union'
      (X := X) (A := A ∪ B) (B := C)
  -- Now take an arbitrary point in the triple union.
  intro x hx
  -- The expression `interior A ∪ interior B ∪ interior C` is parsed as
  -- `(interior A ∪ interior B) ∪ interior C`, so we can case–split.
  cases hx with
  | inl hAB =>
      -- `x` lies in `interior A ∪ interior B`
      have hxAB : (x : X) ∈ interior (A ∪ B) := h₁ hAB
      -- Hence `x` lies in `interior (A ∪ B) ∪ interior C`
      have hx₁ : (x : X) ∈ (interior (A ∪ B) ∪ interior C : Set X) :=
        Or.inl hxAB
      -- Apply the second inclusion.
      exact h₂ hx₁
  | inr hC =>
      -- `x` lies in the `interior C` branch.
      have hx₂ : (x : X) ∈ (interior (A ∪ B) ∪ interior C : Set X) :=
        Or.inr hC
      exact h₂ hx₂

theorem Topology.P3_iff_P1_and_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalence between `P1` and `P3` for open sets.
  have h1 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Existing equivalence between `P1` and `P2` for open sets.
  have h2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP3
    -- Derive `P1` from `P3`, then `P2` from `P1`.
    have hP1 : Topology.P1 A := (h1).mpr hP3
    have hP2 : Topology.P2 A := (h2).mp hP1
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _hP2⟩
    -- Obtain `P3` from `P1`.
    exact (h1).mp hP1

theorem Topology.interiorClosure_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure A) ∪ interior (closure B) ∪ interior (closure C) ⊆
      interior (closure (A ∪ B ∪ C)) := by
  intro x hx
  -- Break the membership in the three‐fold union into cases.
  rcases hx with hxAB | hxC
  · -- `x ∈ interior (closure A) ∪ interior (closure B)`
    rcases hxAB with hxA | hxB
    · -- Subcase: `x ∈ interior (closure A)`
      -- First enlarge to `A ∪ B`.
      have hxAB : (x : X) ∈ interior (closure (A ∪ B)) := by
        have h :=
          Topology.interiorClosure_subset_interiorClosure_union_left
            (X := X) (A := A) (B := B)
        exact h hxA
      -- Then enlarge to `A ∪ B ∪ C`.
      have hABsubset :
          interior (closure (A ∪ B)) ⊆ interior (closure (A ∪ B ∪ C)) := by
        have hSubset : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
          intro y hy
          exact Or.inl hy
        exact
          Topology.interiorClosure_mono
            (X := X) (A := A ∪ B) (B := A ∪ B ∪ C) hSubset
      exact hABsubset hxAB
    · -- Subcase: `x ∈ interior (closure B)`
      have hxAB : (x : X) ∈ interior (closure (A ∪ B)) := by
        have h :=
          Topology.interiorClosure_subset_interiorClosure_union_right
            (X := X) (A := A) (B := B)
        exact h hxB
      have hABsubset :
          interior (closure (A ∪ B)) ⊆ interior (closure (A ∪ B ∪ C)) := by
        have hSubset : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
          intro y hy
          exact Or.inl hy
        exact
          Topology.interiorClosure_mono
            (X := X) (A := A ∪ B) (B := A ∪ B ∪ C) hSubset
      exact hABsubset hxAB
  · -- Case: `x ∈ interior (closure C)`
    have hCsubset :
        interior (closure C) ⊆ interior (closure (A ∪ B ∪ C)) := by
      have hSubset : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      exact
        Topology.interiorClosure_mono
          (X := X) (A := C) (B := A ∪ B ∪ C) hSubset
    exact hCsubset hxC

theorem Topology.closure_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A ∪ B ∪ C : Set X) =
      closure (A : Set X) ∪ closure B ∪ closure C := by
  calc
    closure (A ∪ B ∪ C : Set X)
        = closure ((A ∪ B) ∪ C : Set X) := by
          simpa [Set.union_assoc]
    _ = closure (A ∪ B : Set X) ∪ closure C := by
          simpa [closure_union]
    _ = (closure A ∪ closure B) ∪ closure C := by
          simpa [closure_union]
    _ = closure A ∪ closure B ∪ closure C := by
          simpa [Set.union_assoc]

theorem Topology.closure_union_closure_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure (B : Set X) : Set X) = closure (A ∪ B) := by
  calc
    closure (A ∪ closure (B : Set X) : Set X)
        = closure A ∪ closure (closure (B : Set X)) := by
          simpa using
            (closure_union (A := A) (B := closure (B : Set X)))
    _ = closure A ∪ closure B := by
          simpa [closure_closure]
    _ = closure (A ∪ B : Set X) := by
          simpa using (closure_union (A := A) (B := B)).symm

theorem Topology.interior_subset_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B) := by
  have h_subset : (A : Set X) ⊆ (A ∪ B) := by
    intro x hx
    exact Or.inl hx
  exact interior_mono h_subset

theorem Topology.dense_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → Dense (A ∪ B : Set X) := by
  intro hA_dense
  -- Since `A` is dense, its closure is the whole space.
  have hA_closure : closure (A : Set X) = (Set.univ : Set X) :=
    hA_dense.closure_eq
  -- Hence `closure (A ∪ B)` contains `univ`, because it contains `closure A`.
  have h_superset : (Set.univ : Set X) ⊆ closure (A ∪ B : Set X) := by
    have h_incl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have h_subset : (A : Set X) ⊆ A ∪ B := by
        intro x hx; exact Or.inl hx
      exact closure_mono h_subset
    simpa [hA_closure] using h_incl
  -- The opposite inclusion is trivial.
  have h_subset : closure (A ∪ B : Set X) ⊆ (Set.univ : Set X) := by
    intro x _hx; simp
  -- Therefore `closure (A ∪ B) = univ`, so `A ∪ B` is dense.
  have h_closure_eq : closure (A ∪ B : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm h_subset h_superset
  exact (dense_iff_closure_eq).2 h_closure_eq

theorem Topology.P3_inter_three_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    Topology.P3 (A ∩ B ∩ C) := by
  have h :=
    Topology.isOpen_inter_three_satisfies_P1_P2_P3
      (X := X) (A := A) (B := B) (C := C) hA hB hC
  exact h.2.2

theorem Topology.interiorClosure_union_three_eq
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure (A ∪ B ∪ C : Set X)) =
      interior (closure (A : Set X) ∪ closure B ∪ closure C) := by
  -- First, rewrite using the two–set union lemma with the block `(A ∪ B)` and `C`.
  have h₁ :
      interior (closure ((A ∪ B) ∪ C : Set X)) =
        interior (closure (A ∪ B : Set X) ∪ closure C) := by
    simpa using
      (Topology.interiorClosure_union_eq (X := X) (A := A ∪ B) (B := C))
  -- Next, rewrite `interior (closure (A ∪ B))` using the same lemma for `A` and `B`.
  have h₂ :
      interior (closure (A ∪ B : Set X)) =
        interior (closure (A : Set X) ∪ closure B) := by
    simpa using
      (Topology.interiorClosure_union_eq (X := X) (A := A) (B := B))
  -- Combine the two equalities and simplify with associativity of `∪`.
  simpa [Set.union_assoc, h₂] using h₁

theorem Topology.disjoint_interior_diff_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Disjoint (interior (A \ B : Set X)) (interior B) := by
  refine Set.disjoint_left.2 ?_
  intro x hx_diff hx_intB
  -- `x` lies in `A \ B`, hence it is not in `B`.
  have h_notB : (x : X) ∉ B := by
    have : (x : X) ∈ A \ B :=
      (interior_subset : interior (A \ B) ⊆ A \ B) hx_diff
    exact this.2
  -- But `x` also lies in `interior B`, which is contained in `B`.
  have h_inB : (x : X) ∈ B :=
    (interior_subset : interior B ⊆ B) hx_intB
  exact h_notB h_inB

theorem Topology.closureInterior_union_eq_closure_union_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A ∪ B : Set X)) = closure (A : Set X) ∪ closure B := by
  -- The union of two open sets is open.
  have hAB_open : IsOpen (A ∪ B : Set X) := IsOpen.union hA hB
  -- For an open set, its interior is itself.
  have h_int : interior (A ∪ B : Set X) = A ∪ B := by
    simpa using hAB_open.interior_eq
  -- Rewrite the left‐hand side using `h_int` and simplify with `closure_union`.
  simpa [h_int, closure_union]

theorem Topology.interior_subset_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B) := by
  have h_subset : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  exact interior_mono h_subset

theorem Topology.closureInterior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ∪ closure (interior C) ⊆
      closure (interior (A ∪ B ∪ C)) := by
  intro x hx
  -- Split the triple union into two cases.
  rcases hx with hxAB | hxC
  · -- Case `x ∈ closure (interior A) ∪ closure (interior B)`.
    -- First, use the two–set lemma to upgrade the target set.
    have hxAB' :
        (x : X) ∈ closure (interior (A ∪ B)) :=
      (Topology.closureInterior_union_subset (X := X) (A := A) (B := B)) hxAB
    -- Next, enlarge from `A ∪ B` to `A ∪ B ∪ C` via monotonicity.
    have h_incl :
        closure (interior (A ∪ B)) ⊆
          closure (interior (A ∪ B ∪ C)) := by
      have h_subset : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inl hy
      exact
        Topology.closureInterior_mono
          (X := X) (A := A ∪ B) (B := A ∪ B ∪ C) h_subset
    exact h_incl hxAB'
  · -- Case `x ∈ closure (interior C)`.
    have h_subset : (C : Set X) ⊆ A ∪ B ∪ C := by
      intro y hy
      exact Or.inr hy
    have h_incl :
        closure (interior C) ⊆
          closure (interior (A ∪ B ∪ C)) :=
      Topology.closureInterior_mono
        (X := X) (A := C) (B := A ∪ B ∪ C) h_subset
    exact h_incl hxC

theorem Topology.dense_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (B : Set X) → Dense (A ∪ B : Set X) := by
  intro hDenseB
  have h : Dense (B ∪ A : Set X) := by
    simpa using
      Topology.dense_union_left (X := X) (A := B) (B := A) hDenseB
  simpa [Set.union_comm] using h

theorem Topology.interiorClosure_empty_eq {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simp [closure_empty, interior_empty]

theorem Topology.closureInteriorClosure_empty_eq
    {X : Type*} [TopologicalSpace X] :
    closure (interior (closure (∅ : Set X))) = (∅ : Set X) := by
  simp

theorem Topology.interior_diff_interior_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A \ interior A : Set X) = (∅ : Set X) := by
  -- `interior (A \ interior A)` is an open subset of `A`
  have h_subset_int :
      (interior (A \ interior A : Set X) : Set X) ⊆ interior A := by
    -- First, note it lies in `A`
    have h_sub_A :
        (interior (A \ interior A : Set X) : Set X) ⊆ A := by
      intro x hx
      have hx_diff : (x : X) ∈ A \ interior A :=
        (interior_subset : interior (A \ interior A : Set X) ⊆ A \ interior A) hx
      exact hx_diff.1
    -- Then use maximality of the interior
    exact
      interior_maximal h_sub_A
        (isOpen_interior : IsOpen (interior (A \ interior A : Set X)))
  -- It is also disjoint from `interior A`
  have h_subset_compl :
      (interior (A \ interior A : Set X) : Set X) ⊆ (interior A)ᶜ := by
    intro x hx
    have hx_diff : (x : X) ∈ A \ interior A :=
      (interior_subset : interior (A \ interior A : Set X) ⊆ A \ interior A) hx
    exact hx_diff.2
  -- Hence it is contained in the empty set
  have h_subset_empty :
      (interior (A \ interior A : Set X) : Set X) ⊆ (∅ : Set X) := by
    intro x hx
    have hx_in : (x : X) ∈ interior A := h_subset_int hx
    have hx_not : (x : X) ∉ interior A := h_subset_compl hx
    exact (hx_not hx_in).elim
  -- Equality with `∅`
  exact Set.Subset.antisymm h_subset_empty (Set.empty_subset _)

theorem Topology.P1_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen S) :
    Topology.P1 (⋃₀ 𝒜) := by
  -- Every open set satisfies `P1`.
  have hP1 : ∀ S : Set X, S ∈ 𝒜 → Topology.P1 S := by
    intro S hS
    exact Topology.isOpen_implies_P1 (X := X) (A := S) (h𝒜 S hS)
  -- Apply the existing `P1` lemma for countable unions.
  exact Topology.P1_sUnion (X := X) (𝒜 := 𝒜) hP1

theorem Topology.P3_iff_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  constructor
  · intro hP3
    exact
      Topology.interior_eq_of_isClosed_and_P3
        (X := X) (A := A) hA_closed hP3
  · intro hInt
    have hOpen : IsOpen A := by
      simpa [hInt] using (isOpen_interior : IsOpen (interior A))
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem Topology.eq_univ_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hDense : Dense (A : Set X)) :
    (A : Set X) = (Set.univ : Set X) := by
  -- Use the existing equivalence for closed sets and density.
  exact
    ((Topology.dense_iff_eq_univ_of_isClosed
        (X := X) (A := A) hA_closed).1) hDense

theorem Topology.P1_closure_iff_P1_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (closure A) ↔ Topology.P1 A := by
  -- Since `A` is closed, its closure equals itself.
  have h_eq : (closure A : Set X) = A := hA_closed.closure_eq
  -- Rewriting with this equality shows that the two `P1` statements coincide.
  simpa [h_eq] using
    (Iff.rfl : Topology.P1 (closure A) ↔ Topology.P1 (closure A))

theorem Topology.clopen_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    IsOpen (closure (A : Set X)) ∧ IsClosed (closure A) := by
  exact ⟨h_open, isClosed_closure⟩

theorem Topology.P3_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P3 A := by
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hx_clA, hx_intB⟩
  -- We prove `x ∈ closure (A ∩ B)` using the neighborhood characterization.
  have : (x : X) ∈ closure (A ∩ B) := by
    refine (mem_closure_iff).2 ?_
    intro U hU hxU
    -- The open set `U ∩ interior B` is an open neighbourhood of `x`.
    have hU' : IsOpen (U ∩ interior B) := IsOpen.inter hU isOpen_interior
    have hxU' : (x : X) ∈ U ∩ interior B := ⟨hxU, hx_intB⟩
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have hNonempty : ((U ∩ interior B) ∩ A).Nonempty :=
      (mem_closure_iff).1 hx_clA (U ∩ interior B) hU' hxU'
    rcases hNonempty with ⟨y, ⟨hyU, hy_intB⟩, hyA⟩
    -- The point `y` lies in `B` because it lies in `interior B`.
    have hyB : (y : X) ∈ B := interior_subset hy_intB
    exact ⟨y, hyU, ⟨hyA, hyB⟩⟩
  exact this

theorem Topology.interior_diff_eq_interior_diff_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_closed : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = interior A \ B := by
  ext x
  constructor
  · intro hx
    -- From `x ∈ interior (A \ B)` we get `x ∈ interior A`.
    have hxIntA : (x : X) ∈ interior A := by
      have h_subset : (A \ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact (interior_mono h_subset) hx
    -- And we also have `x ∉ B`.
    have hxNotB : (x : X) ∉ B := by
      have : (x : X) ∈ A \ B :=
        (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hx
      exact this.2
    exact And.intro hxIntA hxNotB
  · rintro ⟨hxIntA, hxNotB⟩
    -- Consider the open neighbourhood `U = interior A ∩ Bᶜ` of `x`.
    have hU_open : IsOpen (interior A ∩ Bᶜ) :=
      IsOpen.inter isOpen_interior hB_closed.isOpen_compl
    have hxU : (x : X) ∈ (interior A ∩ Bᶜ : Set X) :=
      And.intro hxIntA hxNotB
    -- `U` is contained in `A \ B`.
    have hU_subset : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
      intro y hy
      rcases hy with ⟨hyIntA, hyNotB⟩
      have hyA : (y : X) ∈ A := interior_subset hyIntA
      exact And.intro hyA hyNotB
    -- Hence `x ∈ interior (A \ B)`.
    have hU_interior :
        (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B : Set X) :=
      interior_maximal hU_subset hU_open
    exact hU_interior hxU

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) → Topology.P3 A := by
  intro hDense
  -- The closure of a dense set is the whole space, hence open.
  have hOpenClosure : IsOpen (closure (A : Set X)) :=
    Topology.isOpen_closure_of_dense (X := X) (A := A) hDense
  -- An open closure implies `P3` for the original set.
  exact
    Topology.P3_of_isOpen_closure (X := X) (A := A) hOpenClosure

theorem Topology.closureInterior_iterate_idempotent₃
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior A))))))))) =
      closure (interior A) := by
  -- First, use the three–step idempotence lemma on `closure (interior A)`.
  have hStep1 :
      closure (interior (closure (interior (closure (interior
        (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closureInterior_iterate_idempotent
        (X := X) (A := closure (interior A)))
  -- Next, apply the basic idempotence lemma to `A` itself.
  have hStep2 :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using
      (Topology.closureInterior_idempotent (X := X) (A := A))
  -- Combining the two equalities yields the desired result.
  simpa using hStep1.trans hStep2

theorem Topology.Dense.inter_nonempty_of_open
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Dense (A : Set X)) (hU : IsOpen U) (hU_non : U.Nonempty) :
    ((A : Set X) ∩ U).Nonempty := by
  classical
  rcases hU_non with ⟨x, hxU⟩
  -- Since `A` is dense, every point of the space belongs to the closure of `A`.
  have hx_closure : (x : X) ∈ closure (A : Set X) := by
    -- `closure A = univ`
    have h_closure_eq : closure (A : Set X) = (Set.univ : Set X) := hA.closure_eq
    simpa [h_closure_eq] using (by trivial)
  -- Apply the characterization of closure with respect to the open set `U`.
  have h_inter : ((U : Set X) ∩ A).Nonempty :=
    (mem_closure_iff).1 hx_closure U hU hxU
  -- Reorder the intersection to match the goal.
  simpa [Set.inter_comm] using h_inter

theorem Topology.disjoint_interior_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (interior (A : Set X)) (closure (Aᶜ : Set X)) := by
  refine Set.disjoint_left.2 ?_
  intro x hxInt hxCl
  -- `interior A` is an open neighbourhood of `x`.
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Since `x ∈ closure (Aᶜ)`, this neighbourhood meets `Aᶜ`.
  have hNon :
      ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
    (mem_closure_iff).1 hxCl (interior A) hOpen hxInt
  rcases hNon with ⟨y, hyInt, hyComp⟩
  -- But `y ∈ interior A ⊆ A`, contradicting `y ∈ Aᶜ`.
  have : (y : X) ∈ A := interior_subset hyInt
  exact hyComp this

theorem Topology.closureInterior_union_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A ∪ closure (A : Set X))) =
      closure (interior (closure A)) := by
  -- Since `A ⊆ closure A`, the union `A ∪ closure A` is just `closure A`.
  have h_union : (A ∪ closure (A : Set X) : Set X) = closure A := by
    have h_sub : (A : Set X) ⊆ closure A := subset_closure
    exact (Set.union_eq_right.2 h_sub)
  -- Rewriting with this equality yields the desired result.
  simpa [h_union]

theorem Topology.P2_union_isClosed_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 A) (hB_closed : IsClosed B) (hB_P2 : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  -- From `P2 B` and closedness we know that `B` is open.
  have hB_open : IsOpen B :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := B) hB_closed hB_P2
  -- Apply the existing lemma for the union with an open set.
  exact Topology.P2_union_isOpen_right (X := X) (A := A) (B := B) hA hB_open

theorem Topology.dense_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} [Inhabited ι]
    {A : ι → Set X} (hA : ∀ i, Dense (A i)) :
    Dense (⋃ i, A i) := by
  -- We will show that `closure (⋃ i, A i) = univ`.
  have h_subset : (Set.univ : Set X) ⊆ closure (⋃ i, A i : Set X) := by
    -- First, `univ ⊆ ⋃ i, closure (A i)` because each `closure (A i)` is `univ`.
    have h_univ_to_iUnion : (Set.univ : Set X) ⊆ ⋃ i, closure (A i) := by
      intro x _
      classical
      -- Choose an arbitrary index.
      let i₀ : ι := Classical.arbitrary ι
      -- Using density, `closure (A i₀) = univ`, hence `x ∈ closure (A i₀)`.
      have hx : (x : X) ∈ closure (A i₀) := by
        simpa [(hA i₀).closure_eq] using (by simp : (x : X) ∈ (Set.univ : Set X))
      exact Set.mem_iUnion.2 ⟨i₀, hx⟩
    -- Next, apply monotonicity: `⋃ i, closure (A i) ⊆ closure (⋃ i, A i)`.
    exact
      Set.Subset.trans h_univ_to_iUnion
        (Topology.iUnion_closure_subset_closure_iUnion (X := X) (A := A))
  -- We now have both inclusions, so the closures are equal.
  have h_closure_eq :
      closure (⋃ i, A i : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; simp
    · exact h_subset
  -- Finally, translate the closure condition into density.
  exact (dense_iff_closure_eq).2 h_closure_eq

theorem Topology.interior_diff_eq_self_of_open_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_open : IsOpen (A : Set X)) (hB_closed : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = A \ B := by
  have h :=
    Topology.interior_diff_eq_interior_diff_closed
      (X := X) (A := A) (B := B) hB_closed
  simpa [hA_open.interior_eq] using h

theorem Topology.disjoint_closure_interior_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (closure (A : Set X)) (interior (Aᶜ : Set X)) := by
  refine Set.disjoint_left.2 ?_
  intro x hxCl hxInt
  -- `interior (Aᶜ)` is an open neighbourhood of `x`.
  have hOpen : IsOpen (interior (Aᶜ : Set X)) := isOpen_interior
  -- Since `x ∈ closure A`, this neighbourhood meets `A`.
  have hNonempty :
      ((interior (Aᶜ : Set X)) ∩ (A : Set X)).Nonempty :=
    (mem_closure_iff).1 hxCl (interior (Aᶜ)) hOpen hxInt
  rcases hNonempty with ⟨y, hyInt, hyA⟩
  -- But `y ∈ interior (Aᶜ)` implies `y ∈ Aᶜ`, contradicting `y ∈ A`.
  have : (y : X) ∈ (Aᶜ : Set X) :=
    (interior_subset : interior (Aᶜ : Set X) ⊆ Aᶜ) hyInt
  exact this hyA

theorem Topology.P1_iff_P2_and_P3_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  -- Equivalences obtained from the density of `interior A`.
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    (Topology.P2_iff_P1_of_denseInterior (X := X) (A := A) hDense).symm
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    (Topology.P3_iff_P1_of_dense (X := X) (A := A) hDense).symm
  constructor
  · intro hP1
    have hP2 : Topology.P2 A := (hP1P2).1 hP1
    have hP3 : Topology.P3 A := (hP1P3).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    exact (hP1P2).2 hP2

theorem Topology.interior_sUnion_eq_sUnion_of_isOpen
    {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : ∀ S : Set X, S ∈ 𝒜 → IsOpen (S : Set X)) :
    interior (⋃₀ 𝒜 : Set X) = ⋃₀ 𝒜 := by
  have hOpen : IsOpen (⋃₀ 𝒜 : Set X) := isOpen_sUnion h𝒜
  simpa using hOpen.interior_eq

theorem Topology.P2_of_isClosed_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P2 A := by
  -- A closed, dense set is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.P2_of_isClosed_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (interior A)) :
    Topology.P2 A := by
  -- A closed set with dense interior is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_denseInterior
      (X := X) (A := A) hA_closed hDense
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.isClosed_dense_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  have hP2 : Topology.P2 A :=
    Topology.P2_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  have hP3 : Topology.P3 A :=
    Topology.P3_of_isClosed_and_dense (X := X) (A := A) hA_closed hDense
  exact ⟨hP1, hP2, hP3⟩

theorem Topology.closure_union_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∪ B) = closure (A ∪ B) := by
  calc
    closure (closure (A : Set X) ∪ B) =
        closure (closure (A : Set X)) ∪ closure B := by
      simpa using
        (closure_union (A := closure (A : Set X)) (B := B))
    _ = closure A ∪ closure B := by
      simpa [closure_closure]
    _ = closure (A ∪ B) := by
      simpa using (closure_union (A := A) (B := B)).symm

theorem Topology.closureInterior_inter_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A ∩ closure (A : Set X))) = closure (interior A) := by
  have h : (A ∩ closure (A : Set X) : Set X) = A := by
    simpa using
      (Set.inter_eq_left.2 (subset_closure : (A : Set X) ⊆ closure A))
  simpa [h]

theorem Topology.interiorClosure_union_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    interior (closure (A ∪ B : Set X)) = interior (A ∪ B) := by
  -- Since `A ∪ B` is closed, its closure coincides with itself.
  have hClosure : closure (A ∪ B : Set X) = A ∪ B :=
    (IsClosed.union hA hB).closure_eq
  -- Rewriting with `hClosure` gives the desired equality.
  simpa [hClosure]

theorem interior_inter_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior ((A : Set X) ∩ A) = interior A := by
  simpa [Set.inter_self]