

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset
  exact Set.Subset.trans hA h_subset

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono h_closure
  exact Set.Subset.trans hA h_subset

theorem Topology.isOpen_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A := by
  dsimp [Topology.P3]
  exact interior_maximal subset_closure hA

theorem Topology.isOpen_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A := by
  dsimp [Topology.P1]
  simpa [hA.interior_eq] using (subset_closure : A ⊆ closure A)

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior A) h_open

theorem Topology.isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A := by
  dsimp [Topology.P2]
  simpa [hA.interior_eq] using (interior_maximal subset_closure hA)

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_implies_P1 (X := X) (A := interior A) h_open

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_implies_P2 (X := X) (A := interior A) h_open

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_clA : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : A ⊆ A ∪ B))
      exact h_subset hx_clA
  | inr hxB =>
      have hx_clB : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : B ⊆ A ∪ B))
      exact h_subset hx_clB

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure A) := hA hxA
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_left : A ⊆ A ∪ B))
      exact h_subset hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure B) := hB hxB
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_right : B ⊆ A ∪ B))
      exact h_subset hx_int

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hA hB
  dsimp [Topology.P2] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure (interior A)) := hA hxA
      have h_subset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure (interior B)) := hB hxB
      have h_subset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hx_int

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure A)) h_open

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior (closure A)) h_open

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  exact Topology.isOpen_implies_P1 (X := X) (A := interior (closure A)) h_open

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure A = closure (interior A) := by
  intro hA
  apply Set.Subset.antisymm
  ·
    have : closure A ⊆ closure (interior A) :=
      closure_minimal hA isClosed_closure
    exact this
  ·
    exact closure_mono interior_subset

theorem Topology.closure_eq_closure_interior_of_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure A = closure (interior A) := by
  simpa [hA.interior_eq]

theorem Topology.closure_interior_eq_of_P1_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  apply Set.Subset.antisymm
  ·
    have h_subset : interior A ⊆ A := interior_subset
    exact closure_minimal h_subset hClosed
  ·
    exact hP1

theorem Topology.closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → closure A = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P1 (A i)) → Topology.P1 (⋃ i, A i) := by
  intro h_all
  dsimp [Topology.P1] at h_all ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx_cl : x ∈ closure (interior (A i)) := (h_all i) hxA
  have h_subset : closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) := by
    have h_int : interior (A i) ⊆ interior (⋃ i, A i) := by
      have h_sub : (A i) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_sub
    exact closure_mono h_int
  exact h_subset hx_cl

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P3 (A i)) → Topology.P3 (⋃ i, A i) := by
  intro h_all
  dsimp [Topology.P3] at h_all ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx_int : x ∈ interior (closure (A i)) := (h_all i) hxA
  have h_subset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have h_closure : closure (A i) ⊆ closure (⋃ j, A j) := by
      have h_sub : (A i) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_int

theorem Topology.P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  · intro h_eq
    exact fun x hxA => by
      have : x ∈ closure A := subset_closure hxA
      simpa [h_eq] using this

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P2 (⋃ i, A i) := by
  intro h_all
  dsimp [Topology.P2] at h_all ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx_int : x ∈ interior (closure (interior (A i))) := (h_all i) hxA
  have h_subset :
      interior (closure (interior (A i))) ⊆
      interior (closure (interior (⋃ j, A j))) := by
    have h_closure :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      have h_int : interior (A i) ⊆ interior (⋃ j, A j) := by
        have h_sub : (A i) ⊆ ⋃ j, A j := by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i, hy⟩
        exact interior_mono h_sub
      exact closure_mono h_int
    exact interior_mono h_closure
  exact h_subset hx_int

theorem Topology.closure_interior_eq_of_P2_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  have h_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hP2
  have h_cl : closure A = A := hClosed.closure_eq
  simpa [h_cl] using h_eq.symm

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  cases hx

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx

theorem Topology.P3_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hA
    refine ⟨interior (closure A), isOpen_interior, hA, interior_subset⟩
  · rintro ⟨U, hUopen, hAU, hUcl⟩
    dsimp [Topology.P3]
    have hUsubset : U ⊆ interior (closure A) :=
      interior_maximal hUcl hUopen
    exact Set.Subset.trans hAU hUsubset

theorem Topology.P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  -- First, rewrite `hx` using the equality of closures provided by `hP1`.
  have h_cl_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  have hx' : x ∈ closure (interior A) := by
    simpa [h_cl_eq] using hx
  -- Next, use monotonicity to relate the two closures of interiors.
  have h_subset : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h_int : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : A ⊆ closure A)
    exact closure_mono h_int
  exact h_subset hx'

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem Topology.P2_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  constructor
  · intro hP2
    refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
    · exact hP2
    · exact subset_rfl
  · rintro ⟨U, _hUopen, hAU, hUsubset⟩
    dsimp [Topology.P2]
    exact Set.Subset.trans hAU hUsubset

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact Topology.P1_closure (X := X) (A := A) hP1

theorem Topology.P1_iff_closure_interior_eq_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_of_P1_and_isClosed (X := X) (A := A) hP1 hClosed
  · intro h_eq
    dsimp [Topology.P1]
    intro x hx
    simpa [h_eq] using hx

theorem Topology.interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have h_cl_eq := Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hP2
  simpa using congrArg (fun s : Set X => interior s) h_cl_eq

theorem Topology.P3_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · exact Topology.P2_implies_P3 (X := X) (A := A)
  · intro hP3
    dsimp [Topology.P2]
    dsimp [Topology.P3] at hP3
    intro x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    simpa [hA.interior_eq] using hx_int

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  have hP1 : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA
  have hP2 : Topology.P2 A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hA
  constructor
  · intro _; exact hP2
  · intro _; exact hP1

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hx
  exact subset_closure (interior_subset hx)

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    have h_subset : A ⊆ interior A := by
      have : A ⊆ interior (closure A) := hP3
      simpa [hClosed.closure_eq] using this
    have h_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact h_subset
    have h_open : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using h_open
  · intro hOpen
    exact Topology.isOpen_implies_P3 (X := X) (A := A) hOpen

theorem closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact Topology.isOpen_implies_P1 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.interior_closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  have h_cl_eq :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  simpa using congrArg (fun s : Set X => interior s) h_cl_eq

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    exact
      (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  · intro hOpen
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    -- First, show `closure (interior (closure (interior A))) ⊆ closure (interior A)`.
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    -- Now, show `closure (interior A) ⊆ closure (interior (closure (interior A)))`.
    have h₁ : interior A ⊆ interior (closure (interior A)) := by
      have h : interior A ⊆ closure (interior A) := subset_closure
      have : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono h
      simpa [interior_interior] using this
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) : interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  have h_eq :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  simpa [h_eq] using hx

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  exact h₁.trans h₂

theorem Topology.P1_nonempty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior A).Nonempty := by
  intro hP1 hA
  rcases hA with ⟨x, hx⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hx
  classical
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  · have hIntEmpty : interior A = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hInt
    have hFalse : False := by
      have : x ∈ (∅ : Set X) := by
        simpa [hIntEmpty, closure_empty] using hx_cl
      simpa using this
    cases hFalse

theorem Topology.closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have h_subsetA : interior (A ∩ B) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
  have h_subsetB : interior (A ∩ B) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
  have hxA : x ∈ closure (interior A) :=
    (closure_mono h_subsetA) hx
  have hxB : x ∈ closure (interior B) :=
    (closure_mono h_subsetB) hx
  exact And.intro hxA hxB

theorem Topology.closure_interior_eq_univ_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (h_dense : closure A = Set.univ) :
    closure (interior A) = Set.univ := by
  have h_eq := Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  simpa [h_dense] using (h_eq.symm).trans h_dense

theorem Topology.P3_nonempty_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP3 hA
  rcases hA with ⟨x, hxA⟩
  have hx_int : x ∈ interior (closure A) := hP3 hxA
  exact ⟨x, hx_int⟩

theorem Topology.closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ∪ closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_left : A ⊆ A ∪ B))
      exact h_subset hxA
  | inr hxB =>
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (Set.subset_union_right : B ⊆ A ∪ B))
      exact h_subset hxB

theorem Topology.P2_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  exact
    Topology.isOpen_implies_P2 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.closure_interior_eq_univ_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (h_dense : closure A = Set.univ) :
    closure (interior A) = Set.univ := by
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact
    Topology.closure_interior_eq_univ_of_P1 (X := X) (A := A) hP1 h_dense

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  have hP2Open : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  have hP3Open : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  exact hP2Open.trans hP3Open.symm

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} :
    (∀ A, A ∈ S → Topology.P1 A) → Topology.P1 (⋃₀ S) := by
  intro h_all
  dsimp [Topology.P1] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hP1A : Topology.P1 A := h_all A hAS
  have hx_clA : x ∈ closure (interior A) := hP1A hxA
  have hA_subset : A ⊆ ⋃₀ S := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hAS, hy⟩
  have h_int_subset : interior A ⊆ interior (⋃₀ S) :=
    interior_mono hA_subset
  have h_cl_subset : closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
    closure_mono h_int_subset
  exact h_cl_subset hx_clA

theorem Topology.P2_nonempty_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior (closure (interior A))).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact ⟨x, hx⟩

theorem Topology.P1_iff_closure_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact closure_minimal hP1 isClosed_closure
  · intro h_subset
    dsimp [Topology.P1]
    intro x hxA
    have : x ∈ closure A := subset_closure hxA
    exact h_subset this

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  have h₂ : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact Set.Subset.trans h₁ h₂

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} :
    (∀ A, A ∈ S → Topology.P3 A) → Topology.P3 (⋃₀ S) := by
  intro h_all
  dsimp [Topology.P3] at h_all ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hP3A : Topology.P3 A := h_all A hAS
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have hA_subset : A ⊆ ⋃₀ S := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hAS, hy⟩
  have h_closure_subset : closure A ⊆ closure (⋃₀ S) :=
    closure_mono hA_subset
  have h_int_subset : interior (closure A) ⊆ interior (closure (⋃₀ S)) :=
    interior_mono h_closure_subset
  exact h_int_subset hx_int

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} :
    (∀ A, A ∈ S → Topology.P2 A) → Topology.P2 (⋃₀ S) := by
  intro h_all
  dsimp [Topology.P2] at *
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hP2A : Topology.P2 A := h_all A hAS
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hA_subset : A ⊆ ⋃₀ S := by
    intro y hy
    exact Set.mem_sUnion.2 ⟨A, hAS, hy⟩
  have h_int_subset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ S))) := by
    have h_int : interior A ⊆ interior (⋃₀ S) :=
      interior_mono hA_subset
    have h_closure :
        closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
      closure_mono h_int
    exact interior_mono h_closure
  exact h_int_subset hx_int

theorem Topology.interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A) ⊆ A)
  exact interior_mono h_closure

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure A) := by
  exact interior_mono (subset_closure : A ⊆ closure A)

theorem Topology.interior_closure_interior_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Step 1: establish monotone relationships between the pertinent sets.
  have hAB_to_A : interior (A ∩ B) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
  have hAB_to_B : interior (A ∩ B) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
  have h_closure_A : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
    closure_mono hAB_to_A
  have h_closure_B : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
    closure_mono hAB_to_B
  -- Step 2: pass to interiors of the closures.
  have h_int_A : interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) :=
    interior_mono h_closure_A
  have h_int_B : interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior B)) :=
    interior_mono h_closure_B
  -- Step 3: combine the two inclusions for the desired result.
  exact And.intro (h_int_A hx) (h_int_B hx)

theorem Topology.interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  apply Set.Subset.antisymm
  ·
    have h :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h
  ·
    have h_subset : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro x hx
      exact subset_closure hx
    have h_open : IsOpen (interior (closure A)) := isOpen_interior
    have h := interior_maximal h_subset h_open
    simpa using h

theorem Topology.isOpen_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP1A : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA
  exact Topology.P1_closure (X := X) (A := A) hP1A

theorem Topology.closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  exact closure_interior_mono (subset_closure : A ⊆ closure A)

theorem Topology.interior_closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ∪ interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_left : A ⊆ A ∪ B))
      exact h_subset hxA
  | inr hxB =>
      have h_subset : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (Set.subset_union_right : B ⊆ A ∪ B))
      exact h_subset hxB

theorem Topology.interior_closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show `closure (A ∩ B)` is contained in each closure separately.
  have h_closureA : closure (A ∩ B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
  have h_closureB : closure (A ∩ B) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
  -- Pass to interiors via monotonicity.
  have hxA : x ∈ interior (closure A) := (interior_mono h_closureA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono h_closureB) hx
  exact And.intro hxA hxB

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → closure A = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    -- Show `closure A ⊆ closure (interior (closure A))`.
    have h₁ : A ⊆ closure (interior (closure A)) := by
      intro x hxA
      have hx_int : x ∈ interior (closure A) := hP3 hxA
      exact subset_closure hx_int
    exact closure_minimal h₁ isClosed_closure
  ·
    -- The reverse inclusion follows from monotonicity.
    have h₂ : interior (closure A) ⊆ closure A := interior_subset
    have h₃ : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono h₂
    simpa [closure_closure] using h₃

theorem Topology.closure_eq_closure_interior_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A = closure (interior (closure A)) := by
  intro hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact
    Topology.closure_eq_closure_interior_closure_of_P3 (X := X) (A := A) hP3

theorem Topology.closure_eq_closure_interior_union_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 A → Topology.P1 B →
      closure (A ∪ B) = closure (interior (A ∪ B)) := by
  intro hA hB
  -- Obtain `P1` for the union from the hypotheses on `A` and `B`.
  have hUnion : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Translate `P1` for the union into the desired equality of closures.
  exact Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := A ∪ B) hUnion

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (Set.univ : Set X) := by
  have hOpen : IsOpen (Set.univ : Set X) := isOpen_univ
  exact Topology.isOpen_implies_P3 (X := X) (A := Set.univ) hOpen

theorem Topology.interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interior_closure_interior_closure_eq (X := X) (A := interior A))

theorem Topology.closure_interior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- We will show `x` lies in each `closure (interior (A i))`.
  have hxi : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- First observe the basic inclusion `(⋂ j, A j) ⊆ A i`.
    have h_subset₁ : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Pass to interiors using monotonicity.
    have h_subset₂ : interior (⋂ j, A j) ⊆ interior (A i) :=
      interior_mono h_subset₁
    -- Finally, pass to closures.
    exact (closure_mono h_subset₂) hx
  -- Package the pointwise memberships into an intersection.
  exact Set.mem_iInter.2 hxi

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x _
  simp [interior_univ, closure_univ]

theorem Topology.closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
      simpa using
        Topology.closure_interior_closure_interior_eq_closure_interior
          (X := X) (A := closure (interior A))
    _ = closure (interior A) := by
      simpa using
        Topology.closure_interior_closure_interior_eq_closure_interior
          (X := X) (A := A)

theorem Topology.interior_closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- Establish the monotone relationships needed to transfer `hx`.
    have h_subset₁ : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_subset₂ : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset₁
    have h_subset₃ : interior (closure (⋂ j, A j)) ⊆ interior (closure (A i)) :=
      interior_mono h_subset₂
    exact h_subset₃ hx
  exact Set.mem_iInter.2 hx_i

theorem Topology.interior_closure_interior_closure_interior_eq
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

theorem Topology.interior_eq_of_P3_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hClosed : IsClosed A) :
    interior A = A := by
  apply Set.Subset.antisymm
  · exact interior_subset
  ·
    have : A ⊆ interior (closure A) := hP3
    simpa [hClosed.closure_eq] using this

theorem Topology.closure_interior_closure_eq_univ_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (h_dense : closure A = Set.univ) :
    closure (interior (closure A)) = Set.univ := by
  -- First, relate the two closures via `P3`.
  have h_eq :=
    Topology.closure_eq_closure_interior_closure_of_P3
      (X := X) (A := A) hP3
  -- Rewrite the equality so that the desired set appears on the left.
  have h_symm : closure (interior (closure A)) = closure A := by
    simpa using h_eq.symm
  -- Combine with the density hypothesis to reach the conclusion.
  simpa [h_dense] using h_symm

theorem Topology.closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP1
  -- Step 1: obtain the equality of interiors of closures from `P1`.
  have h_int_eq :=
    Topology.interior_closure_eq_of_P1 (X := X) (A := A) hP1
  -- Step 2: apply `closure` to both sides of the equality.
  have h_closure_eq :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) :=
    congrArg (fun s : Set X => closure s) h_int_eq
  -- Step 3: use the idempotent property to rewrite the right–hand side.
  have h_target :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  -- Step 4: conclude by combining the two equalities.
  simpa [h_target] using h_closure_eq

theorem Topology.interior_closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (closure (A i))) ⊆ interior (closure (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_closure : closure (A i) ⊆ closure (⋃ j, A j) := by
    have h_subset : A i ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact closure_mono h_subset
  have h_subset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure
  exact h_subset hx_i

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = Set.univ → Topology.P3 A := by
  intro h_dense
  dsimp [Topology.P3]
  intro x hxA
  have : (x : X) ∈ interior (closure A) := by
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_dense, interior_univ] using this
  exact this

theorem Topology.P1_nonempty_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP1 hA
  -- Obtain a point in `interior A` from `P1` and the nonemptiness of `A`.
  have hIntA : (interior A).Nonempty :=
    Topology.P1_nonempty_interior (X := X) (A := A) hP1 hA
  rcases hIntA with ⟨x, hxIntA⟩
  -- Use monotonicity to see that this point also lies in `interior (closure A)`.
  have hxIntCl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
  exact ⟨x, hxIntCl⟩

theorem Topology.interior_closure_interior_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First, pass to interiors using monotonicity.
  have h₁ : interior A ⊆ interior B := interior_mono hAB
  -- Next, take closures, preserving the inclusion.
  have h₂ : closure (interior A) ⊆ closure (interior B) := closure_mono h₁
  -- Finally, take interiors again to obtain the desired inclusion.
  exact interior_mono h₂

theorem Topology.closure_interior_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  have h_diff_subset : (A \ B) ⊆ A := Set.diff_subset
  have h_int_subset : interior (A \ B) ⊆ interior A :=
    interior_mono h_diff_subset
  exact closure_mono h_int_subset

theorem Topology.closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  simpa [closure_closure] using h₂

theorem Topology.closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) = closure (interior (closure A)) := by
  simpa using
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := closure A)

theorem Topology.P2_nonempty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  -- `P2` supplies a point of `interior (closure (interior A))`.
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  classical
  -- Either `interior A` is nonempty, in which case we are done, or it is empty,
  -- in which case we derive a contradiction from `hx`.
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  ·
    have hIntEmpty : interior A = (∅ : Set X) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hInt
    have : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty, interior_empty] using hx
    exact False.elim (Set.not_mem_empty _ this)

theorem Topology.interior_closure_interior_union_subset {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure (interior A))`.
      have h_subset : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- First, upgrade the inclusion from interiors to closures.
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          -- Since `A ⊆ A ∪ B`, we obtain `interior A ⊆ interior (A ∪ B)`.
          have h_int : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
          -- Taking closures preserves this inclusion.
          exact closure_mono h_int
        -- Passing to interiors yields the desired inclusion.
        exact interior_mono h_closure
      exact h_subset hxA
  | inr hxB =>
      -- Handle the symmetric case `x ∈ interior (closure (interior B))`.
      have h_subset : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          have h_int : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
          exact closure_mono h_int
        exact interior_mono h_closure
      exact h_subset hxB

theorem Topology.closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simp

theorem Topology.interior_eq_of_P2_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hClosed : IsClosed A) :
    interior A = A := by
  -- First, deduce `P3 A` from the given `P2 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Apply the existing result for `P3` sets that are closed.
  exact
    Topology.interior_eq_of_P3_and_isClosed (X := X) (A := A) hP3 hClosed

theorem Topology.P1_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P1 A := by
  intro h_closure
  dsimp [Topology.P1]
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_closure] using this

theorem Topology.P1_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (U ∩ A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  rcases hx with ⟨hxU, hxA⟩
  have hx_cl : x ∈ closure (interior A) := hP1 hxA
  -- First, prove `x ∈ closure (U ∩ interior A)`.
  have hx_cl₂ : x ∈ closure (U ∩ interior A) := by
    -- Use the neighbourhood characterization of the closure.
    have h_mem_closure := (mem_closure_iff).1 hx_cl
    have h_goal : ∀ V, IsOpen V → x ∈ V → (V ∩ (U ∩ interior A)).Nonempty := by
      intro V hV hxV
      -- Intersect the neighbourhood with `U`, which is open and contains `x`.
      have hVU_open : IsOpen (V ∩ U) := hV.inter hU
      have hxVU : x ∈ V ∩ U := ⟨hxV, hxU⟩
      -- Apply the characterization of `hx_cl`.
      have h_nonempty : (V ∩ U ∩ interior A).Nonempty :=
        h_mem_closure (V ∩ U) hVU_open hxVU
      -- Rearrange the intersection to match the goal.
      simpa [Set.inter_assoc, Set.inter_left_comm] using h_nonempty
    exact (mem_closure_iff).2 h_goal
  -- Next, upgrade to `closure (interior (U ∩ A))` via monotonicity.
  have h_subset : (U ∩ interior A) ⊆ interior (U ∩ A) := by
    have h_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
    have h_sub : (U ∩ interior A) ⊆ U ∩ A := by
      intro y hy
      exact ⟨hy.1, interior_subset hy.2⟩
    exact interior_maximal h_sub h_open
  have hx_final : x ∈ closure (interior (U ∩ A)) := by
    have h_closure_mono : closure (U ∩ interior A) ⊆ closure (interior (U ∩ A)) :=
      closure_mono h_subset
    exact h_closure_mono hx_cl₂
  exact hx_final

theorem Topology.P2_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (U ∩ A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hxUA
  rcases hxUA with ⟨hxU, hxA⟩
  -- `P2 A` supplies a neighbourhood of `x` inside `closure (interior A)`.
  have hx_intA : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Consider the open neighbourhood `V := interior (closure (interior A)) ∩ U` of `x`.
  set V : Set X := interior (closure (interior A)) ∩ U with hVdef
  have hV_open : IsOpen V := (isOpen_interior).inter hU
  have hxV : x ∈ V := by
    have : x ∈ interior (closure (interior A)) ∧ x ∈ U := ⟨hx_intA, hxU⟩
    simpa [hVdef] using this
  -- We show that every point of `V` lies in `closure (interior (U ∩ A))`.
  have hV_subset : V ⊆ closure (interior (U ∩ A)) := by
    intro y hyV
    have hy_intA : y ∈ interior (closure (interior A)) := by
      have : y ∈ V := hyV
      have : y ∈ interior (closure (interior A)) ∧ y ∈ U := by
        simpa [hVdef] using this
      exact this.1
    have hyU : y ∈ U := by
      have : y ∈ V := hyV
      have : y ∈ interior (closure (interior A)) ∧ y ∈ U := by
        simpa [hVdef] using this
      exact this.2
    -- Convert membership in the interior of the closure to the closure itself.
    have hy_closure_intA : y ∈ closure (interior A) :=
      interior_subset hy_intA
    -- Use the neighbourhood characterisation of the closure to prove
    -- `y ∈ closure (interior (U ∩ A))`.
    have : y ∈ closure (interior (U ∩ A)) := by
      -- Reformulate via `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro W hWopen hyW
      -- Intersect the neighbourhood with `U`, which is open and contains `y`.
      have hWU_open : IsOpen (W ∩ U) := hWopen.inter hU
      have hyWU : y ∈ W ∩ U := ⟨hyW, hyU⟩
      -- Since `y ∈ closure (interior A)`, this neighbourhood meets `interior A`.
      have h_nonempty : (W ∩ U ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hy_closure_intA (W ∩ U) hWU_open hyWU
      -- `U` is open, so `U ∩ interior A` sits inside `interior (U ∩ A)`.
      have h_subset : U ∩ interior A ⊆ interior (U ∩ A) := by
        have h_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
        have h_sub : U ∩ interior A ⊆ U ∩ A := by
          intro z hz
          exact ⟨hz.1, interior_subset hz.2⟩
        exact interior_maximal h_sub h_open
      -- Hence the neighbourhood meets `interior (U ∩ A)`.
      have : (W ∩ interior (U ∩ A)).Nonempty := by
        rcases h_nonempty with ⟨z, ⟨hzW, hzU⟩, hzIntA⟩
        have hzIntUA : z ∈ interior (U ∩ A) := h_subset ⟨hzU, hzIntA⟩
        exact ⟨z, ⟨hzW, hzIntUA⟩⟩
      exact this
    exact this
  -- `V` is an open neighbourhood of `x` contained in the target set,
  -- hence `x` is in the interior.
  have : x ∈ interior (closure (interior (U ∩ A))) :=
    (interior_maximal hV_subset hV_open) hxV
  exact this

theorem Topology.closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : interior A ⊆ A)

theorem Topology.closure_interior_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (interior (A i))) ⊆ closure (interior (⋃ i, A i)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- Establish the inclusion needed to transfer `hx_i`.
  have h_closure :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    -- First, relate the interiors through monotonicity.
    have h_int : interior (A i) ⊆ interior (⋃ j, A j) := by
      have h_subset : (A i) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    -- Taking closures preserves the inclusion.
    exact closure_mono h_int
  exact h_closure hx_i

theorem Topology.P3_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (U ∩ A) := by
  intro hP3
  dsimp [Topology.P3] at hP3 ⊢
  intro x hxUA
  rcases hxUA with ⟨hxU, hxA⟩
  have hxInt : x ∈ interior (closure A) := hP3 hxA
  -- Define an open neighbourhood of `x` that we will eventually place inside
  -- `closure (U ∩ A)`.
  have hV_open : IsOpen (interior (closure A) ∩ U) :=
    isOpen_interior.inter hU
  have hxV : x ∈ interior (closure A) ∩ U := ⟨hxInt, hxU⟩
  -- Show that this neighbourhood is actually contained in `closure (U ∩ A)`.
  have hV_subset : (interior (closure A) ∩ U) ⊆ closure (U ∩ A) := by
    intro y hy
    have hyInt : y ∈ interior (closure A) := hy.1
    have hyU  : y ∈ U := hy.2
    have hyClA : y ∈ closure A := interior_subset hyInt
    -- Use the neighbourhood characterization of the closure.
    have : y ∈ closure (U ∩ A) := by
      apply (mem_closure_iff).2
      intro V hVopen hyV
      have hVU_open : IsOpen (V ∩ U) := hVopen.inter hU
      have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      have h_nonempty : (V ∩ U ∩ A).Nonempty :=
        (mem_closure_iff).1 hyClA (V ∩ U) hVU_open hyVU
      simpa [Set.inter_assoc, Set.inter_left_comm] using h_nonempty
    exact this
  -- Conclude that `x` lies in the desired interior.
  exact
    (interior_maximal hV_subset hV_open) hxV

theorem Topology.P3_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (A ∩ U) := by
  intro hP3
  have h := Topology.P3_inter_open_left (X := X) (U := U) (A := A) hU hP3
  simpa [Set.inter_comm] using h

theorem Topology.interior_closure_eq_univ_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure A = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  simpa [h_dense, interior_univ]

theorem Topology.P1_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (A ∩ U) := by
  intro hP1
  have h := Topology.P1_inter_open_left (X := X) (U := U) (A := A) hU hP1
  simpa [Set.inter_comm] using h

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  have h₁ : closure A ⊆ closure B := closure_mono hAB
  have h₂ : interior (closure A) ⊆ interior (closure B) := interior_mono h₁
  exact closure_mono h₂



theorem Topology.interior_closure_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hA.closure_eq]

theorem Topology.closure_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]

theorem Topology.closure_interior_closure_interior_eq_closure_interior'
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    -- First, prove `closure (interior (closure (interior A))) ⊆ closure (interior A)`.
    have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  ·
    -- Now, prove the reverse inclusion.
    have h₁ : interior A ⊆ interior (closure (interior A)) := by
      have h : interior A ⊆ closure (interior A) := subset_closure
      have : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono h
      simpa [interior_interior] using this
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h₁
    exact h₂

theorem Topology.closure_union_interior_eq_union_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (interior A) (interior B)

theorem Topology.interior_closure_closure_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.closure_iUnion_interior_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (⋃ i, interior (A i)) ⊆ closure (interior (⋃ i, A i)) := by
  -- Every `interior (A i)` is contained in `interior (⋃ i, A i)`.
  have h_subset : (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
    have h_incl : interior (A i) ⊆ interior (⋃ j, A j) :=
      interior_mono (Set.subset_iUnion (fun j ↦ A j) i)
    exact h_incl hx_int
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset

theorem Topology.P2_interior_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (closure (interior (closure (interior A))))) := by
  have h_open :
      IsOpen (interior (closure (interior (closure (interior A))))) :=
    isOpen_interior
  exact
    Topology.isOpen_implies_P2
      (X := X)
      (A := interior (closure (interior (closure (interior A)))))
      h_open

theorem Topology.isOpen_of_P2_and_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hClosed : IsClosed A) : IsOpen A := by
  have h_eq : interior A = A :=
    Topology.interior_eq_of_P2_and_isClosed (X := X) (A := A) hP2 hClosed
  have h_open_int : IsOpen (interior A) := isOpen_interior
  simpa [h_eq] using h_open_int

theorem Topology.closure_interior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior A) = closure A := by
  simpa [hA.interior_eq]

theorem Topology.P2_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (A ∩ U) := by
  intro hP2
  have h := Topology.P2_inter_open_left (X := X) (U := U) (A := A) hU hP2
  simpa [Set.inter_comm] using h

theorem interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∪ B) = interior (A ∪ B) := rfl

theorem Topology.closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (Aᶜ) = (interior A)ᶜ := by
  classical
  ext x
  constructor
  · intro hx
    -- We show that `x ∉ interior A`.
    by_cases hxInt : x ∈ interior A
    · -- Derive a contradiction from `hx` and `hxInt`.
      have h_nonempty :=
        (mem_closure_iff).1 hx (interior A) isOpen_interior hxInt
      rcases h_nonempty with ⟨y, hy⟩
      have h_inA  : y ∈ A     := interior_subset hy.1
      have h_notA : y ∈ Aᶜ := hy.2
      have : False := h_notA h_inA
      exact (this.elim)
    · -- If `x ∉ interior A`, this is exactly the desired statement.
      exact hxInt
  · intro hx
    -- Here `hx` is `x ∉ interior A`; we prove `x ∈ closure (Aᶜ)`.
    have hNotInt : x ∉ interior A := hx
    -- Use the neighbourhood characterisation of the closure.
    have h_closure : x ∈ closure (Aᶜ) := by
      apply (mem_closure_iff).2
      intro U hUopen hxU
      -- We must show `(U ∩ Aᶜ).Nonempty`.
      by_contra h_empty
      -- `h_empty` says `U ⊆ A`.
      have h_sub : U ⊆ A := by
        intro y hyU
        by_contra hyNotA
        have h_inter : (U ∩ Aᶜ).Nonempty := ⟨y, ⟨hyU, hyNotA⟩⟩
        exact h_empty h_inter
      -- Hence `U ⊆ interior A` (since `U` is open and contained in `A`).
      have hU_interior : U ⊆ interior A :=
        interior_maximal h_sub hUopen
      -- This puts `x` in `interior A`, contradicting `hNotInt`.
      have : x ∈ interior A := hU_interior hxU
      exact (hNotInt this).elim
    exact h_closure

theorem Set.compl_compl {α : Type*} (s : Set α) : sᶜᶜ = (s : Set α) := by
  ext x
  simp

theorem Topology.closure_eq_closure_interior_closure_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A = closure (interior (closure A)) := by
  intro hP1
  -- First, rewrite `closure A` using `P1`.
  have h₁ :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  -- Next, relate the two closures of interiors via `P1`.
  have h₂ :=
    Topology.closure_interior_closure_eq_closure_interior_of_P1
      (X := X) (A := A) hP1
  -- Chain the equalities together.
  calc
    closure A = closure (interior A) := h₁
    _ = closure (interior (closure A)) := h₂.symm

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (Aᶜ) = (closure A)ᶜ := by
  -- First, rewrite `closure A` in terms of `interior (Aᶜ)` using an existing lemma.
  have h₁ : closure A = (interior (Aᶜ))ᶜ := by
    -- Apply the lemma for the complement set `Aᶜ`.
    have h := Topology.closure_compl_eq_compl_interior (X := X) (A := Aᶜ)
    simpa [Set.compl_compl] using h
  -- Take complements of both sides of `h₁` to obtain the desired equality.
  have h₂ : interior (Aᶜ) = (closure A)ᶜ := by
    have := congrArg (fun s : Set X => sᶜ) h₁
    simpa [Set.compl_compl] using this.symm
  simpa using h₂

theorem Topology.closure_interior_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∩ closure (Aᶜ) = (∅ : Set X) := by
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  calc
    interior A ∩ closure (Aᶜ) =
        interior A ∩ (interior A)ᶜ := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa [Set.inter_compl_self]

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h_subset : interior A ⊆ A := interior_subset
  exact closure_minimal h_subset hA

theorem Topology.closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∩ interior (Aᶜ) = (∅ : Set X) := by
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  calc
    closure A ∩ interior (Aᶜ) = closure A ∩ (closure A)ᶜ := by
      simpa [h]
    _ = (∅ : Set X) := by
      simpa [Set.inter_compl_self]

theorem Topology.interior_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  calc
    interior A ∪ closure (Aᶜ) = interior A ∪ (interior A)ᶜ := by
      simpa [h]
    _ = (Set.univ : Set X) := by
      simpa [Set.union_compl_self]

theorem Topology.closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  simpa [h_dense, interior_univ, closure_univ]

theorem Topology.interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ)) = (closure (interior A))ᶜ := by
  -- First, rewrite `closure (Aᶜ)` using the complement–interior relation.
  have h₁ := Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Chain equalities, finishing with the complement–closure relation for `interior A`.
  calc
    interior (closure (Aᶜ))
        = interior ((interior A)ᶜ) := by
          simpa [h₁]
    _ = (closure (interior A))ᶜ := by
          simpa using
            (Topology.interior_compl_eq_compl_closure
              (X := X) (A := interior A))

theorem Topology.interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ interior A`; use monotonicity `interior_mono`.
      have h_subset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact h_subset hxA
  | inr hxB =>
      -- `x ∈ interior B`; similar argument.
      have h_subset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
      exact h_subset hxB

theorem Topology.closure_union_interior_compl_eq_univ {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure A ∪ interior (Aᶜ) = (Set.univ : Set X) := by
  -- Rewrite `interior (Aᶜ)` in terms of the complement of `closure A`.
  have h : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- The union of a set with its complement is the whole space.
  calc
    closure A ∪ interior (Aᶜ) = closure A ∪ (closure A)ᶜ := by
      simpa [h]
    _ = (Set.univ : Set X) := by
      simpa [Set.union_compl_self]

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- Identify the closure of the interior of our target set with the set itself.
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := closure A)
  -- Rewrite `hx` using the above equality to obtain the desired membership.
  have hx' : x ∈ closure (interior (closure (interior (closure A)))) := by
    simpa [h_eq] using hx
  exact hx'

theorem Topology.closure_compl_eq_univ_iff_interior_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (Aᶜ : Set X) = Set.univ ↔ interior A = (∅ : Set X) := by
  -- The basic relation between closure of a complement and interior.
  have h_rel := Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  constructor
  · intro h_cl
    -- Rewrite `h_cl` using `h_rel` to get an equality of complements.
    have h_compl : (interior A)ᶜ = (Set.univ : Set X) := by
      simpa [h_rel] using h_cl
    -- Complement both sides to deduce `interior A = ∅`.
    have : interior A = (∅ : Set X) := by
      simpa using congrArg (fun s : Set X => sᶜ) h_compl
    simpa using this
  · intro h_int
    -- Substitute `h_int` into `h_rel` to obtain the desired equality.
    simpa [h_int] using h_rel

theorem Topology.interior_eq_compl_closure_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A = (closure (Aᶜ : Set X))ᶜ := by
  -- Start with `closure (Aᶜ) = (interior A)ᶜ`.
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Complement both sides to relate to `interior A`.
  have h' : (closure (Aᶜ : Set X))ᶜ = interior A := by
    simpa [Set.compl_compl] using congrArg (fun s : Set X => sᶜ) h
  -- Rearrange to obtain the desired equality.
  simpa [Set.compl_compl] using h'.symm

theorem Topology.P3_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (U ∪ A) := by
  intro hP3A
  have hP3U : Topology.P3 U :=
    Topology.isOpen_implies_P3 (X := X) (A := U) hU
  simpa using
    Topology.P3_union (X := X) (A := U) (B := A) hP3U hP3A

theorem Topology.interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem Topology.interior_diff_closure_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A \ closure A = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxInt, hxNotCl⟩
    have hxCl : x ∈ closure A := subset_closure (interior_subset hxInt)
    exact (hxNotCl hxCl).elim
  · intro hx
    cases hx

theorem Topology.P1_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∪ interior B) := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior).union isOpen_interior
  exact
    Topology.isOpen_implies_P1 (X := X) (A := interior A ∪ interior B) h_open

theorem Topology.interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A :=
    (interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)) hx
  have hxB : x ∈ interior B :=
    (interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)) hx
  exact And.intro hxA hxB

theorem Topology.P3_and_isClosed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hClosed : IsClosed A) : Topology.P1 A := by
  -- From `hP3` and the closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- Open sets satisfy `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A = (Set.univ : Set X) → interior (Aᶜ) = (∅ : Set X) := by
  intro h_dense
  have h_eq : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [h_dense] using h_eq

theorem Topology.interior_inter_interior_compl_eq_empty' {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior A ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxA, hxAc⟩
    have hA : x ∈ A := interior_subset hxA
    have hAc : x ∈ Aᶜ := interior_subset hxAc
    exact (hAc hA).elim
  · exact Set.empty_subset _

theorem Topology.P1_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (U ∪ A) := by
  intro hP1A
  have hP1U : Topology.P1 U :=
    Topology.isOpen_implies_P1 (X := X) (A := U) hU
  exact Topology.P1_union (X := X) (A := U) (B := A) hP1U hP1A

theorem Topology.P1_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set Y} (hA : IsOpen A) :
    Topology.P1 (f ⁻¹' A) := by
  have h_open : IsOpen (f ⁻¹' A) := hA.preimage hf
  exact Topology.isOpen_implies_P1 (X := X) (A := f ⁻¹' A) h_open

theorem Topology.P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set Y} (hA : IsOpen A) :
    Topology.P2 (f ⁻¹' A) := by
  have h_open : IsOpen (f ⁻¹' A) := hA.preimage hf
  exact Topology.isOpen_implies_P2 (X := X) (A := f ⁻¹' A) h_open

theorem Topology.closure_eq_compl_interior_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A = (interior (Aᶜ))ᶜ := by
  have h := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  have h' := congrArg (fun s : Set X => sᶜ) h
  simpa [Set.compl_compl] using h'.symm

theorem Topology.interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A ∩ closure A) = interior A := by
  apply Set.Subset.antisymm
  ·
    -- The interior of the intersection is contained in `A`, hence in `interior A`.
    have h : (A ∩ closure A) ⊆ A := Set.inter_subset_left
    exact interior_mono h
  ·
    -- `interior A` is an open subset of the intersection, so it lies in its interior.
    have h_subset : interior A ⊆ A ∩ closure A := by
      intro x hx
      have hxA : x ∈ A := interior_subset hx
      have hxCl : x ∈ closure A := subset_closure hxA
      exact And.intro hxA hxCl
    exact interior_maximal h_subset isOpen_interior

theorem Topology.P2_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (U ∪ A) := by
  intro hP2A
  have hP2U : Topology.P2 U :=
    Topology.isOpen_implies_P2 (X := X) (A := U) hU
  simpa using
    Topology.P2_union (X := X) (A := U) (B := A) hP2U hP2A

theorem Topology.interior_eq_univ_iff_closure_compl_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (Set.univ : Set X) ↔ closure (Aᶜ) = (∅ : Set X) := by
  -- Core relation between the two sets
  have h_rel : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  constructor
  · intro hInt
    -- Substitute `interior A = univ` into the core relation
    simpa [hInt] using h_rel
  · intro hCl
    -- Use `h_rel` and the hypothesis `closure (Aᶜ) = ∅`
    have h_compl : (interior A)ᶜ = (∅ : Set X) := by
      simpa [hCl] using h_rel.symm
    -- Complement both sides to get `interior A = univ`
    have hInt : interior A = (∅ : Set X)ᶜ := by
      have := congrArg (fun s : Set X => sᶜ) h_compl
      simpa using this
    simpa using hInt

theorem Topology.isClosed_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure : IsClosed (closure (interior A)))

theorem Topology.closure_inter_interiors_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure (interior A) := by
    have h_subset : interior A ∩ interior B ⊆ interior A :=
      Set.inter_subset_left
    exact (closure_mono h_subset) hx
  have hxB : x ∈ closure (interior B) := by
    have h_subset : interior A ∩ interior B ⊆ interior B :=
      Set.inter_subset_right
    exact (closure_mono h_subset) hx
  exact And.intro hxA hxB

theorem Topology.P3_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set Y} (hA : IsOpen A) :
    Topology.P3 (f ⁻¹' A) := by
  have h_open : IsOpen (f ⁻¹' A) := hA.preimage hf
  exact Topology.isOpen_implies_P3 (X := X) (A := f ⁻¹' A) h_open

theorem Topology.closure_interior_inter_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ∩ interior (Aᶜ) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxClInt, hxIntCompl⟩
    -- `closure (interior A)` sits inside `closure A`.
    have h_closure_mono :
        closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (X := X) (A := A)
    have hxClA : x ∈ closure A := h_closure_mono hxClInt
    -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
    have h_eq :
        interior (Aᶜ) = (closure A)ᶜ :=
      Topology.interior_compl_eq_compl_closure (X := X) (A := A)
    have hxNotClA : x ∈ (closure A)ᶜ := by
      simpa [h_eq] using hxIntCompl
    -- Contradiction.
    exact (hxNotClA hxClA).elim
  · exact Set.empty_subset _

theorem Topology.interior_closure_inter_closure_interior_compl_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) ∩ closure (interior (Aᶜ)) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxIntClA, hxClIntCompl⟩
    -- `interior (closure A)` is an open neighbourhood of `x`.
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    -- Since `x ∈ closure (interior (Aᶜ))`, this neighbourhood meets `interior (Aᶜ)`.
    rcases
        (mem_closure_iff).1 hxClIntCompl (interior (closure A)) hOpen hxIntClA
      with ⟨y, ⟨hyIntClA, hyIntCompl⟩⟩
    -- But `interior (closure A) ⊆ closure A`.
    have hyClA : y ∈ closure A := interior_subset hyIntClA
    -- Hence `y ∈ closure A ∩ interior (Aᶜ)`, contradicting
    -- `closure A ∩ interior (Aᶜ) = ∅`.
    have hFalse : False := by
      have hEmpty :=
        Topology.closure_inter_interior_compl_eq_empty (X := X) (A := A)
      have : y ∈ (∅ : Set X) := by
        simpa [hEmpty] using And.intro hyClA hyIntCompl
      simpa using this
    exact False.elim hFalse
  · exact Set.empty_subset _

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    interior (U ∩ A) = U ∩ interior A := by
  apply Set.Subset.antisymm
  · -- `interior (U ∩ A) ⊆ U ∩ interior A`
    intro x hx
    have hxUA : x ∈ U ∩ A := interior_subset hx
    have hxU : x ∈ U := hxUA.1
    have hxIntA : x ∈ interior A := by
      have h_mono : interior (U ∩ A) ⊆ interior A :=
        interior_mono (Set.inter_subset_right : (U ∩ A) ⊆ A)
      exact h_mono hx
    exact And.intro hxU hxIntA
  · -- `U ∩ interior A ⊆ interior (U ∩ A)`
    intro x hx
    rcases hx with ⟨hxU, hxIntA⟩
    -- Define the open set `U ∩ interior A`.
    have h_open : IsOpen (U ∩ interior A) := hU.inter isOpen_interior
    -- It sits inside `U ∩ A`.
    have h_subset : (U ∩ interior A) ⊆ (U ∩ A) := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    -- Hence every point of `U ∩ interior A` belongs to the interior of `U ∩ A`.
    have h_into : (U ∩ interior A) ⊆ interior (U ∩ A) :=
      interior_maximal h_subset h_open
    exact h_into ⟨hxU, hxIntA⟩

theorem Topology.interior_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ closure (interior A) := by
  intro x hx
  exact subset_closure hx

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)) hx
  have hxB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)) hx
  exact And.intro hxA hxB

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    have hSub : interior A ⊆ (∅ : Set X) := by
      have : interior A ⊆ closure (interior A) := subset_closure
      simpa [h] using this
    -- A set contained in `∅` is `∅`.
    ext x
    constructor
    · intro hx
      have : x ∈ (∅ : Set X) := hSub hx
      simpa using this
    · intro hx
      cases hx
  · intro h
    calc
      closure (interior A) = closure (∅ : Set X) := by
        simpa [h]
      _ = (∅ : Set X) := by
        simp

theorem Topology.closure_interior_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  simpa [Set.compl_compl] using
    (Topology.closure_interior_inter_interior_compl_eq_empty
      (X := X) (A := Aᶜ))

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- `interior A` is open and included in its closure.
  have h_open : IsOpen (interior A) := isOpen_interior
  have h_subset : interior A ⊆ closure (interior A) := subset_closure
  -- Apply `interior_maximal` to obtain the desired inclusion.
  exact interior_maximal h_subset h_open

theorem Topology.interior_compl_eq_univ_iff_closure_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ) = (Set.univ : Set X) ↔ closure A = (∅ : Set X) := by
  -- Relate the two sets using the existing complement–closure lemma.
  have h_rel := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  constructor
  · intro hInt
    -- Translate `hInt` via `h_rel` to obtain `(closure A)ᶜ = univ`.
    have h_eq : (closure A)ᶜ = (Set.univ : Set X) := by
      simpa [h_rel] using hInt
    -- Complement both sides to deduce `closure A = ∅`.
    have h_closure : closure A = (Set.univ : Set X)ᶜ := by
      simpa using congrArg (fun s : Set X => sᶜ) h_eq
    simpa [Set.compl_univ] using h_closure
  · intro hCl
    -- Rewrite `interior (Aᶜ)` using `h_rel` and `hCl`.
    have h_eq : interior (Aᶜ) = (closure A)ᶜ := h_rel
    simpa [hCl, Set.compl_empty] using h_eq

theorem Topology.isClosed_closure_diff_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure A \ interior A) := by
  have h₁ : IsClosed (closure A) := isClosed_closure
  have h₂ : IsClosed ((interior A)ᶜ) :=
    (isOpen_interior : IsOpen (interior A)).isClosed_compl
  -- `A \ B` is definitionally `A ∩ Bᶜ`, so this is an intersection of two closed sets.
  simpa [Set.diff_eq] using h₁.inter h₂

theorem Topology.continuous_closure_preimage_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f)
    {B : Set Y} :
    closure (f ⁻¹' B) ⊆ f ⁻¹' closure B := by
  intro x hx
  -- `hx` gives a neighbourhood criterion for `x` with respect to `f ⁻¹' B`.
  have h_closure :
      ∀ V : Set X, IsOpen V → x ∈ V → (V ∩ (f ⁻¹' B)).Nonempty :=
    (mem_closure_iff).1 hx
  -- We will verify the neighbourhood criterion for `f x` and `B`.
  have h_goal :
      ∀ W : Set Y, IsOpen W → f x ∈ W → (W ∩ B).Nonempty := by
    intro W hWopen hfxW
    -- The preimage of `W` is an open neighbourhood of `x`.
    have h_preimage_open : IsOpen (f ⁻¹' W) := hWopen.preimage hf
    have hx_preimage : x ∈ f ⁻¹' W := hfxW
    -- Apply the closure criterion at `x`.
    have h_nonempty :
        ((f ⁻¹' W) ∩ (f ⁻¹' B)).Nonempty :=
      h_closure (f ⁻¹' W) h_preimage_open hx_preimage
    -- Map the witness forward via `f`.
    rcases h_nonempty with ⟨y, hy⟩
    rcases hy with ⟨hyW, hyB⟩
    exact ⟨f y, And.intro hyW hyB⟩
  -- Conclude that `f x` is in the closure of `B`.
  have h_fx : f x ∈ closure B := (mem_closure_iff).2 h_goal
  simpa using h_fx

theorem Topology.image_closure_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' closure A ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxCl, rfl⟩
  -- We will verify the neighbourhood criterion for `f x`.
  refine (mem_closure_iff).2 ?_
  intro V hVopen hfxV
  -- The preimage of `V` is an open neighbourhood of `x`.
  have hPreOpen : IsOpen (f ⁻¹' V) := hVopen.preimage hf
  have hxPre : x ∈ f ⁻¹' V := hfxV
  -- Since `x ∈ closure A`, this neighbourhood meets `A`.
  have hNonempty : ((f ⁻¹' V) ∩ A).Nonempty :=
    (mem_closure_iff).1 hxCl (f ⁻¹' V) hPreOpen hxPre
  rcases hNonempty with ⟨z, hzPre, hzA⟩
  -- Map the witness forward to obtain a point in `V ∩ f '' A`.
  exact ⟨f z, And.intro hzPre ⟨z, hzA, rfl⟩⟩

theorem Topology.closure_closure_interior_closure_eq {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (closure (interior (closure A))) = closure (interior (closure A)) := by
  simpa using
    (Topology.closure_closure_interior (X := X) (A := closure A))

theorem Topology.interior_iInter_closure_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, closure (A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- Show membership in each component of the intersection.
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- The intersection is contained in each individual closure.
    have h_subset : (⋂ j, closure (A j)) ⊆ closure (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Pass to interiors via monotonicity.
    have h_int_subset :
        interior (⋂ j, closure (A j)) ⊆ interior (closure (A i)) :=
      interior_mono h_subset
    exact h_int_subset hx
  exact Set.mem_iInter.2 hx_i



theorem Topology.interior_closure_diff_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A \ B)) ⊆ interior (closure A) := by
  have h_closure : closure (A \ B) ⊆ closure A :=
    closure_mono (Set.diff_subset : A \ B ⊆ A)
  exact interior_mono h_closure

theorem Topology.P3_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (A ∪ U) := by
  intro hP3A
  have hP3U : Topology.P3 U :=
    Topology.isOpen_implies_P3 (X := X) (A := U) hU
  simpa using
    Topology.P3_union (X := X) (A := A) (B := U) hP3A hP3U

theorem Topology.P3_and_isClosed_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hClosed : IsClosed A) : Topology.P2 A := by
  have hEquiv := (Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed)
  exact hEquiv.mpr hP3

theorem Topology.P2_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (A ∪ U) := by
  intro hP2A
  have h := Topology.P2_union_open_left (X := X) (U := U) (A := A) hU hP2A
  simpa [Set.union_comm] using h

theorem Set.Subset_univ {α : Type*} {s : Set α} : s ⊆ (Set.univ : Set α) := by
  intro x _
  simp

theorem Topology.interior_closure_union_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  have h : closure (A ∪ B) = closure A ∪ closure B := by
    simpa using closure_union A B
  simpa [h]

theorem Topology.nonempty_interior_iff_nonempty_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty ↔ (closure (interior A)).Nonempty := by
  constructor
  · intro hInt
    exact hInt.closure
  · intro hCl
    classical
    by_cases hInt : (interior A).Nonempty
    · exact hInt
    ·
      have hIntEmpty : interior A = (∅ : Set X) := by
        simpa [Set.not_nonempty_iff_eq_empty] using hInt
      have hContrad : False := by
        -- `hCl` gives a point in `closure (interior A)`, but this set is empty.
        have : (∅ : Set X).Nonempty := by
          simpa [hIntEmpty, closure_empty] using hCl
        simpa using this
      exact False.elim hContrad

theorem Topology.closure_interior_union_interior_closure_compl_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ∪ interior (closure (Aᶜ)) = (Set.univ : Set X) := by
  have h :
      interior (closure (Aᶜ)) = (closure (interior A))ᶜ :=
    Topology.interior_closure_compl_eq_compl_closure_interior (X := X) (A := A)
  calc
    closure (interior A) ∪ interior (closure (Aᶜ))
        = closure (interior A) ∪ (closure (interior A))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa [Set.union_compl_self]

theorem Topology.closure_inter_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ interior B) ⊆ A)) hx
  have hxIntB : x ∈ closure (interior B) :=
    (closure_mono (Set.inter_subset_right : (A ∩ interior B) ⊆ interior B)) hx
  exact And.intro hxA hxIntB

theorem Topology.closure_inter_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∩ B) = A ∩ B := by
  have hClosed : IsClosed (A ∩ B) := hA.inter hB
  simpa using hClosed.closure_eq

theorem Topology.interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  exact interior_mono (Set.diff_subset : A \ B ⊆ A)

theorem Topology.closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ)) = (interior (closure A))ᶜ := by
  -- First rewrite `interior (Aᶜ)` using an existing complement–closure lemma.
  have h₁ : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Apply the closure–interior complement lemma to `closure A`.
  have h₂ : closure ((closure A)ᶜ) = (interior (closure A))ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := closure A)
  -- Combine the two equalities.
  simpa [h₁] using h₂

theorem Topology.P1_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (A ∪ U) := by
  intro hP1A
  have h := Topology.P1_union_open_left (X := X) (U := U) (A := A) hU hP1A
  simpa [Set.union_comm] using h

theorem Topology.isOpen_of_P3_and_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hClosed : IsClosed A) : IsOpen A := by
  exact
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3

theorem Topology.P2_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Topology.P2 A := by
  intro h_closure
  dsimp [Topology.P2]
  intro x hxA
  -- Since `closure (interior A) = univ`, its interior is also `univ`.
  have h_int : interior (closure (interior A)) = (Set.univ : Set X) := by
    simpa [h_closure, interior_univ]
  -- Any point of `A` (indeed, any point at all) lies in this interior.
  have : (x : X) ∈ interior (closure (interior A)) := by
    simpa [h_int] using (by
      have : (x : X) ∈ (Set.univ : Set X) := by
        simp
      exact this)
  exact this

theorem Topology.closure_interior_eq_of_P3_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  -- From `hP3` and the closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- Hence `interior A = A`.
  have h_int : interior A = A := hOpen.interior_eq
  -- Rewrite and simplify.
  calc
    closure (interior A) = closure A := by
      simpa [h_int]
    _ = A := hClosed.closure_eq

theorem Topology.interior_inter_eq_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B) = interior A ∩ interior B := by
  apply Set.Subset.antisymm
  · -- `interior (A ∩ B)` is contained in each interior separately.
    exact Topology.interior_inter_subset (X := X) (A := A) (B := B)
  · -- The reverse inclusion: an open set inside `A ∩ B` yields membership in the interior.
    intro x hx
    -- `interior A ∩ interior B` is open.
    have h_open : IsOpen (interior A ∩ interior B) :=
      isOpen_interior.inter isOpen_interior
    -- It sits inside `A ∩ B`.
    have h_subset : interior A ∩ interior B ⊆ (A ∩ B) := by
      intro y hy
      exact And.intro (interior_subset hy.1) (interior_subset hy.2)
    -- Hence its points belong to `interior (A ∩ B)`.
    exact (interior_maximal h_subset h_open) hx

theorem Topology.P2_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior A ∪ interior B) := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior).union isOpen_interior
  exact
    Topology.isOpen_implies_P2 (X := X) (A := interior A ∪ interior B) h_open

theorem Topology.interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ⊆ interior (A ∪ B) := by
  exact interior_mono (Set.subset_union_left : A ⊆ A ∪ B)

theorem Topology.closure_interior_eq_of_isOpen_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hOpen : IsOpen A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  calc
    closure (interior A) = closure A := by
      simpa [hOpen.interior_eq]
    _ = A := hClosed.closure_eq

theorem Topology.interior_union_interior_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (interior A ∪ interior B) = interior A ∪ interior B := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union isOpen_interior
  simpa using h_open.interior_eq

theorem Topology.closure_interior_diff_interior_subset_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior A ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxClInt, hxNotInt⟩
  -- Use the monotonicity of `closure` to move from `closure (interior A)` to `closure A`.
  have hxClA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (X := X) (A := A)) hxClInt
  exact And.intro hxClA hxNotInt

theorem Topology.preimage_interior_subset_interior {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {B : Set Y} :
    f ⁻¹' interior B ⊆ interior (f ⁻¹' B) := by
  -- The preimage of an open set under a continuous map is open.
  have h_open : IsOpen (f ⁻¹' interior B) :=
    (isOpen_interior : IsOpen (interior B)).preimage hf
  -- Since `interior B ⊆ B`, their preimages satisfy the same inclusion.
  have h_subset : f ⁻¹' interior B ⊆ f ⁻¹' B := by
    intro x hx
    dsimp [Set.preimage] at hx ⊢
    exact interior_subset hx
  -- Any open subset of `f ⁻¹' B` is contained in its interior.
  exact interior_maximal h_subset h_open

theorem Topology.image_interior_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {A : Set X} :
    f '' interior A ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxInt, rfl⟩
  have : f x ∈ f '' A := ⟨x, interior_subset hxInt, rfl⟩
  exact subset_closure this

theorem Topology.interior_closure_compl_inter_closure_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (Aᶜ)) ∩ closure (interior A) = (∅ : Set X) := by
  have h :
      interior (closure (Aᶜ)) = (closure (interior A))ᶜ :=
    Topology.interior_closure_compl_eq_compl_closure_interior (X := X) (A := A)
  calc
    interior (closure (Aᶜ)) ∩ closure (interior A)
        = (closure (interior A))ᶜ ∩ closure (interior A) := by
          simpa [h]
    _ = (∅ : Set X) := by
          simpa [Set.inter_compl_self]

theorem Topology.closure_interior_inter_eq_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) = closure (interior A ∩ interior B) := by
  have h := Topology.interior_inter_eq_inter (X := X) (A := A) (B := B)
  simpa using congrArg (fun s : Set X => closure s) h

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  have h_eq : closure (closure A) = closure (interior (closure A)) := by
    calc
      closure (closure A) = closure A := by
        simpa [closure_closure]
      _ = closure (interior (closure A)) := by
        simpa using
          (Topology.closure_eq_closure_interior_closure_of_P3
            (X := X) (A := A) hP3)
  exact
    (Topology.P1_iff_closure_eq_closure_interior
        (X := X) (A := closure A)).2 h_eq



theorem Topology.closure_diff_interior_eq_closure_inter_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior A = closure A ∩ closure (Aᶜ) := by
  classical
  have h : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  calc
    closure A \ interior A
        = closure A ∩ (interior A)ᶜ := by
          simp [Set.diff_eq]
    _ = closure A ∩ closure (Aᶜ) := by
          simpa [h]

theorem Topology.closure_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- First, `x` lies in the closure of `A`.
  have hxClA : x ∈ closure A :=
    (closure_mono (Set.diff_subset : A \ B ⊆ A)) hx
  -- Next, show that `x ∉ interior B`.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Since `x ∈ closure (A \ B)`, every neighbourhood of `x` meets `A \ B`.
    have h_nonempty :
        (interior B ∩ (A \ B)).Nonempty := by
      have h_open : IsOpen (interior B) := isOpen_interior
      exact (mem_closure_iff).1 hx (interior B) h_open hxIntB
    rcases h_nonempty with ⟨y, hyIntB, hyDiff⟩
    -- But `y ∈ interior B` implies `y ∈ B`, contradicting `y ∉ B`.
    have : y ∈ B := interior_subset hyIntB
    exact (hyDiff.2 this).elim
  exact And.intro hxClA hxNotIntB

theorem Topology.interior_iUnion_interior_eq {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋃ i, interior (A i)) = ⋃ i, interior (A i) := by
  have h_open : IsOpen (⋃ i, interior (A i)) := by
    refine isOpen_iUnion (fun _ => isOpen_interior)
  simpa using h_open.interior_eq

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    interior (A ∩ U) = interior A ∩ U := by
  have h :=
    Topology.interior_inter_open_left (X := X) (U := U) (A := A) hU
  simpa [Set.inter_comm] using h

theorem Topology.interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty, interior_empty]



theorem Topology.closure_eq_closure_interior_closure_of_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure A = closure (interior (closure A)) := by
  have hP3 : Topology.P3 A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hA
  exact
    Topology.closure_eq_closure_interior_closure_of_P3
      (X := X) (A := A) hP3

theorem Topology.closure_eq_univ_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  ·
    exact (Set.Subset_univ : closure A ⊆ (Set.univ : Set X))
  ·
    have h_sub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (X := X) (A := A)
    simpa [h] using h_sub

theorem Topology.interior_closure_inter_closure_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) :=
    (interior_mono
        (Set.inter_subset_left : (closure A ∩ closure B) ⊆ closure A)) hx
  have hxB : x ∈ interior (closure B) :=
    (interior_mono
        (Set.inter_subset_right : (closure A ∩ closure B) ⊆ closure B)) hx
  exact And.intro hxA hxB

theorem Topology.closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- Show that `x` belongs to the closure of each `A i`.
  have hx_i : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The intersection is contained in each component `A i`.
    have h_subset : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking closures preserves inclusions.
    have h_closure : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure hx
  -- Package the pointwise memberships into an intersection.
  exact Set.mem_iInter.2 hx_i

theorem Topology.interior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    interior (⋂ i, A i) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- Show `x` belongs to each `interior (A i)`.
  have hxi : ∀ i, x ∈ interior (A i) := by
    intro i
    -- The intersection is contained in each component `A i`.
    have h_subset : (⋂ j, A j) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Pass to interiors using monotonicity.
    have h_int_subset : interior (⋂ j, A j) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_int_subset hx
  exact Set.mem_iInter.2 hxi

theorem Topology.interior_closure_inter_interiors_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `A ∩ interior B` sits inside `A`, hence its closure sits inside `closure A`.
  have h_closureA : closure (A ∩ interior B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ interior B) ⊆ A)
  -- Likewise, `A ∩ interior B` is contained in `B`, since `interior B ⊆ B`.
  have h_closureB : closure (A ∩ interior B) ⊆ closure B := by
    have h_subset : (A ∩ interior B) ⊆ B := by
      intro y hy
      exact interior_subset hy.2
    exact closure_mono h_subset
  -- Pass to interiors via monotonicity.
  have hxA : x ∈ interior (closure A) := (interior_mono h_closureA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono h_closureB) hx
  exact And.intro hxA hxB

theorem Topology.closure_diff_interior_eq_self_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (A \ interior A) = A \ interior A := by
  -- First, prove the set `A \ interior A` is closed.
  have hClosed : IsClosed (A \ interior A) := by
    -- `A` is closed by hypothesis, and `(interior A)ᶜ` is closed as the complement of an open set.
    have hIntCompl : IsClosed ((interior A)ᶜ) :=
      (isOpen_interior : IsOpen (interior A)).isClosed_compl
    -- The intersection of two closed sets is closed; rewrite the set difference as such an intersection.
    simpa [Set.diff_eq] using hA.inter hIntCompl
  -- The closure of a closed set is itself.
  simpa using hClosed.closure_eq

theorem Topology.interior_inter_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have h_cl : x ∈ closure A := subset_closure (interior_subset hx)
    exact And.intro hx h_cl

theorem Topology.interior_inter_open_left_closure {X : Type*} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) :
    interior (U ∩ closure A) = U ∩ interior (closure A) := by
  simpa using
    (Topology.interior_inter_open_left (X := X) (U := U) (A := closure A) hU)

theorem Topology.interior_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ closure B) :
    interior A ⊆ closure B := by
  intro x hx
  exact hAB (interior_subset hx)

theorem Topology.closure_interior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem Topology.closure_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ interior A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hCl => exact hCl
    | inr hInt =>
        exact subset_closure (interior_subset hInt)
  · intro x hx
    exact Or.inl hx

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- Step 1: obtain the equality of interiors provided by `P2`.
  have h_int_eq :=
    Topology.interior_closure_eq_of_P2 (X := X) (A := A) hP2
  -- Step 2: apply `closure` to both sides of the equality.
  have h_cl_eq :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) :=
    congrArg (fun s : Set X => closure s) h_int_eq
  -- Step 3: simplify the right–hand side using the idempotent property.
  have h_simp :=
    Topology.closure_interior_closure_interior_eq_closure_interior
      (X := X) (A := A)
  -- Step 4: conclude by rewriting.
  simpa [h_simp] using h_cl_eq

theorem Topology.interior_closure_preimage_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {B : Set Y} :
    interior (closure (f ⁻¹' B)) ⊆ f ⁻¹' closure B := by
  intro x hx
  -- From `hx`, we know `x` lies in the interior of `closure (f ⁻¹' B)`.
  have hx_cl : x ∈ closure (f ⁻¹' B) := interior_subset hx
  -- Apply the previously proven inclusion for closures.
  have h_subset :
      closure (f ⁻¹' B) ⊆ f ⁻¹' closure B :=
    Topology.continuous_closure_preimage_subset (X := X) (Y := Y)
      (f := f) hf (B := B)
  exact h_subset hx_cl

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  have hx_int_cl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hx
  exact subset_closure hx_int_cl

theorem Topology.interior_closure_inter_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ∩ closure A = interior (closure A) := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact And.intro hx (interior_subset hx)

theorem Topology.interior_diff_eq_diff_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A \ B) = A \ closure B := by
  calc
    interior (A \ B) = interior (A ∩ Bᶜ) := by
      simpa [Set.diff_eq]
    _ = A ∩ interior (Bᶜ) := by
      simpa using
        Topology.interior_inter_open_left (X := X) (U := A) (A := Bᶜ) hA
    _ = A ∩ (closure B)ᶜ := by
      simpa [Topology.interior_compl_eq_compl_closure (X := X) (A := B)]
    _ = A \ closure B := by
      simpa [Set.diff_eq]

theorem Topology.closure_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B) ⊆ closure A := by
  exact closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)

theorem Topology.closure_image_interior_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {A : Set X} :
    closure (f '' interior A) ⊆ closure (f '' A) := by
  -- First, note the obvious inclusion `f '' interior A ⊆ f '' A`.
  have h_subset : f '' interior A ⊆ f '' A := by
    intro y hy
    rcases hy with ⟨x, hxInt, rfl⟩
    exact ⟨x, interior_subset hxInt, rfl⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset

theorem Topology.interior_closure_union_closure_interior_compl_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) ∪ closure (interior (Aᶜ)) = (Set.univ : Set X) := by
  have h :
      closure (interior (Aᶜ)) = (interior (closure A))ᶜ :=
    Topology.closure_interior_compl_eq_compl_interior_closure
      (X := X) (A := A)
  calc
    interior (closure A) ∪ closure (interior (Aᶜ))
        = interior (closure A) ∪ (interior (closure A))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa [Set.union_compl_self]

theorem Topology.isClosed_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (closure (interior (closure A))) := by
  -- `closure (interior (closure A))` is a closure, hence closed.
  exact isClosed_closure

theorem Topology.closure_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  -- First, note the inclusion `A ⊆ A ∪ B`, and pass to interiors.
  have h : interior A ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
  -- Taking closures preserves set inclusion.
  exact closure_mono h

theorem Topology.P2_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  constructor
  · intro hP2
    exact
      Topology.interior_eq_of_P2_and_isClosed (X := X) (A := A) hP2 hClosed
  · intro hInt
    -- From `interior A = A` we obtain that `A` is open.
    have hOpen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [hInt] using this
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen

theorem Topology.interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆ interior (closure (A ∩ B)) := by
  -- First, record the obvious inclusion between the underlying sets.
  have h_subset : A ∩ interior B ⊆ A ∩ B := by
    intro x hx
    rcases hx with ⟨hxA, hxIntB⟩
    exact And.intro hxA (interior_subset hxIntB)
  -- Monotonicity of `closure` upgrades the inclusion.
  have h_closure : closure (A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono h_subset
  -- Finally, pass to interiors using monotonicity once more.
  exact interior_mono h_closure

theorem Topology.boundary_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior A = closure (Aᶜ) \ interior (Aᶜ) := by
  classical
  have h₁ : closure (Aᶜ) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  have h₂ : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [Set.diff_eq, h₁, h₂, Set.inter_comm, Set.compl_compl]

theorem Topology.closure_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (∅ : Set X) ↔ A = (∅ : Set X) := by
  constructor
  · intro h
    have h₁ : A ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure A := subset_closure hx
      simpa [h] using this
    exact Set.Subset.antisymm h₁ (Set.empty_subset _)
  · intro hA
    simpa [hA, closure_empty]

theorem Topology.boundary_eq_diff_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure A \ interior A = A \ interior A := by
  simpa [hA.closure_eq]

theorem Topology.closure_inter_subset_closed_left
    {X : Type*} [TopologicalSpace X] {U A : Set X} (hU : IsClosed U) :
    closure (U ∩ A) ⊆ U := by
  have h_subset : closure (U ∩ A) ⊆ closure U :=
    closure_mono (Set.inter_subset_left : (U ∩ A) ⊆ U)
  simpa [hU.closure_eq] using h_subset



theorem Topology.boundary_union_subset_union_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ B) \ interior (A ∪ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  intro x hx
  rcases hx with ⟨hxClUnion, hxNotIntUnion⟩
  -- Express `x ∈ closure (A ∪ B)` in terms of the closures of the summands.
  have hCl : x ∈ closure A ∪ closure B := by
    have h_eq : closure (A ∪ B) = closure A ∪ closure B := by
      simpa using closure_union A B
    simpa [h_eq] using hxClUnion
  -- Distinguish the two cases of the union.
  cases hCl with
  | inl hxClA =>
      -- Show that `x ∉ interior A`, otherwise we contradict `hxNotIntUnion`.
      have hxNotIntA : x ∉ interior A := by
        intro hxIntA
        have hxIntUnion : x ∈ interior (A ∪ B) := by
          have h_subset : interior A ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
          exact h_subset hxIntA
        exact hxNotIntUnion hxIntUnion
      exact Or.inl ⟨hxClA, hxNotIntA⟩
  | inr hxClB =>
      -- Analogous argument for the second summand.
      have hxNotIntB : x ∉ interior B := by
        intro hxIntB
        have hxIntUnion : x ∈ interior (A ∪ B) := by
          have h_subset : interior B ⊆ interior (A ∪ B) :=
            interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
          exact h_subset hxIntB
        exact hxNotIntUnion hxIntUnion
      exact Or.inr ⟨hxClB, hxNotIntB⟩

theorem Topology.compl_boundary_eq_union_interior_compl_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (closure A \ interior A)ᶜ = interior A ∪ (closure A)ᶜ := by
  classical
  ext x
  simp [Set.diff_eq, Set.compl_inter, Set.compl_compl, Set.union_comm]

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∩ interior B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxIntB⟩
  -- We will verify the neighbourhood criterion for `x` with respect to `A ∩ B`.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- Intersect the given neighbourhood with `interior B`, which is open and contains `x`.
  have hUI_open : IsOpen (U ∩ interior B) := hUopen.inter isOpen_interior
  have hx_UI : x ∈ U ∩ interior B := ⟨hxU, hxIntB⟩
  -- Since `x ∈ closure A`, this new neighbourhood meets `A`.
  have h_nonempty : ((U ∩ interior B) ∩ A).Nonempty :=
    (mem_closure_iff).1 hxClA (U ∩ interior B) hUI_open hx_UI
  -- Re-package the witness to lie in `U ∩ (A ∩ B)`.
  rcases h_nonempty with ⟨y, ⟨hyU, hyIntB⟩, hyA⟩
  refine ⟨y, ?_⟩
  have hyB : y ∈ B := interior_subset hyIntB
  exact ⟨hyU, ⟨hyA, hyB⟩⟩

theorem Topology.nonempty_interior_closure_of_nonempty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty → (interior (closure A)).Nonempty := by
  intro hIntA
  rcases hIntA with ⟨x, hxIntA⟩
  have hxIntCl : x ∈ interior (closure A) :=
    (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
  exact ⟨x, hxIntCl⟩

theorem Topology.image_closure_interior_subset_closure_image_interior
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' closure (interior A) ⊆ closure (f '' interior A) := by
  simpa using
    Topology.image_closure_subset_closure_image
      (X := X) (Y := Y) (f := f) hf (A := interior A)

theorem Topology.closure_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (closure A \ interior A) = closure A \ interior A := by
  -- The set `closure A \ interior A` is closed, hence equal to its closure.
  have hClosed : IsClosed (closure A \ interior A) :=
    Topology.isClosed_closure_diff_interior (X := X) (A := A)
  simpa using hClosed.closure_eq

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotClB⟩
  -- We show that `x ∈ closure (A \ B)` using the neighbourhood criterion.
  have : x ∈ closure (A \ B) := by
    apply (mem_closure_iff).2
    intro U hUopen hxU
    -- Intersect the neighbourhood with the open complement of `closure B`.
    have hOpenCompl : IsOpen ((closure (B : Set X))ᶜ) :=
      (isClosed_closure : IsClosed (closure B)).isOpen_compl
    have hVopen : IsOpen (U ∩ (closure (B : Set X))ᶜ) :=
      hUopen.inter hOpenCompl
    have hxV : x ∈ U ∩ (closure (B : Set X))ᶜ :=
      ⟨hxU, hxNotClB⟩
    -- Since `x ∈ closure A`, this open set meets `A`.
    have hNonempty :
        (U ∩ (closure (B : Set X))ᶜ ∩ A).Nonempty :=
      (mem_closure_iff).1 hxClA _ hVopen hxV
    rcases hNonempty with ⟨y, ⟨hyU, hyNotClB⟩, hyA⟩
    -- The point `y` avoids `B`, hence lies in `A \ B`.
    have hyNotB : y ∉ B := by
      intro hyB
      have : y ∈ (closure (B : Set X)) := subset_closure hyB
      exact hyNotClB this
    exact ⟨y, ⟨hyU, ⟨hyA, hyNotB⟩⟩⟩
  exact this

theorem Topology.closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i)) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_sub : (A i) ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_closure_sub : closure (A i) ⊆ closure (⋃ j, A j) :=
    closure_mono h_sub
  exact h_closure_sub hx_i

theorem Topology.boundary_eq_closure_diff_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure A \ interior A = closure A \ A := by
  simpa [hA.interior_eq]

theorem Topology.interior_closure_compl_inter_interior_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (Aᶜ)) ∩ interior A = (∅ : Set X) := by
  classical
  -- Step 1: rewrite `interior (closure (Aᶜ))` using an existing lemma.
  have h₁ :
      interior (closure (Aᶜ)) = (closure (interior A))ᶜ :=
    Topology.interior_closure_compl_eq_compl_closure_interior
      (X := X) (A := A)
  -- Step 2: show that the right–hand side is empty.
  have h₂ :
      (closure (interior A))ᶜ ∩ interior A = (∅ : Set X) := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨hxNot, hxInt⟩
      have hxCl : x ∈ closure (interior A) := subset_closure hxInt
      exact (hxNot hxCl).elim
    · exact Set.empty_subset _
  -- Step 3: combine the equalities.
  simpa [h₁, h₂]

theorem Topology.image_interior_closure_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' interior (closure A) ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hxIntClA, rfl⟩
  -- From `hxIntClA : x ∈ interior (closure A)`, deduce `x ∈ closure A`.
  have hxClA : x ∈ closure A := interior_subset hxIntClA
  -- Apply the existing inclusion for images of closures.
  have h_image_closure :=
    Topology.image_closure_subset_closure_image
      (X := X) (Y := Y) (f := f) hf (A := A)
  -- Since `f x ∈ f '' closure A`, the desired conclusion follows.
  exact h_image_closure ⟨x, hxClA, rfl⟩

theorem Topology.closure_union_closure_right_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure B) = closure (A ∪ B) := by
  simpa [closure_union, closure_closure]

theorem Topology.closure_union_closure_left_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ B) = closure (A ∪ B) := by
  calc
    closure (closure A ∪ B)
        = closure (B ∪ closure A) := by
          simpa [Set.union_comm]
    _ = closure (B ∪ A) := by
          simpa using
            Topology.closure_union_closure_right_eq_closure_union
              (X := X) (A := B) (B := A)
    _ = closure (A ∪ B) := by
          simpa [Set.union_comm]

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_closure : (x : X) ∈ closure A := subset_closure hxA
  simpa [h.interior_eq] using hx_closure

theorem Topology.closure_diff_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B) ⊆ closure A := by
  exact closure_mono (Set.diff_subset : A \ B ⊆ A)

theorem Topology.closure_compl_eq_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure (Aᶜ : Set X) = Aᶜ := by
  simpa [hA.interior_eq] using
    (Topology.closure_compl_eq_compl_interior (X := X) (A := A))

theorem Topology.closure_union_closures_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ closure B) = closure (A ∪ B) := by
  have h₁ :
      closure (closure A ∪ closure B) = closure (A ∪ closure B) := by
    simpa using
      Topology.closure_union_closure_left_eq_closure_union
        (X := X) (A := A) (B := closure B)
  have h₂ : closure (A ∪ closure B) = closure (A ∪ B) := by
    simpa using
      Topology.closure_union_closure_right_eq_closure_union
        (X := X) (A := A) (B := B)
  simpa [h₁] using h₂

theorem Topology.interior_closure_union_closure_right_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ closure B)) = interior (closure (A ∪ B)) := by
  have h :=
    Topology.closure_union_closure_right_eq_closure_union
      (X := X) (A := A) (B := B)
  simpa using congrArg (fun s : Set X => interior s) h

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3cl
  dsimp [Topology.P3] at hP3cl ⊢
  intro x hxA
  have hxCl : (x : X) ∈ closure A := subset_closure hxA
  have hxInt : x ∈ interior (closure (closure A)) := hP3cl hxCl
  simpa [closure_closure] using hxInt



theorem Topology.interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior (closure A) ⊆ closure A := by
  simpa using (interior_subset : interior (closure A) ⊆ closure A)

theorem Topology.closure_interior_compl_inter_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (Aᶜ)) ∩ interior (closure A) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hContr : False := by
      rcases hx with ⟨hxClIntCompl, hxIntClA⟩
      -- `interior (closure A)` is an open neighbourhood of `x`.
      have hOpen : IsOpen (interior (closure A)) := isOpen_interior
      -- Hence it meets `interior (Aᶜ)`.
      have hNonempty :
          ((interior (closure A)) ∩ interior (Aᶜ)).Nonempty :=
        (mem_closure_iff).1 hxClIntCompl (interior (closure A)) hOpen hxIntClA
      rcases hNonempty with ⟨y, ⟨hyIntClA, hyIntCompl⟩⟩
      -- But `interior (closure A) ⊆ closure A`.
      have hyClA : y ∈ closure A := interior_subset hyIntClA
      -- This contradicts `closure A ∩ interior (Aᶜ) = ∅`.
      have hEmpty :=
        Topology.closure_inter_interior_compl_eq_empty (X := X) (A := A)
      have : y ∈ (∅ : Set X) := by
        simpa [hEmpty] using And.intro hyClA hyIntCompl
      exact this
    exact (False.elim hContr)
  · exact Set.empty_subset _



theorem Topology.boundary_inter_subset_union_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B) \ interior (A ∩ B) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) := by
  intro x hx
  rcases hx with ⟨hxClAB, hxNotIntAB⟩
  -- `x` lies in the closure of each factor.
  have hxClA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : A ∩ B ⊆ A)) hxClAB
  have hxClB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : A ∩ B ⊆ B)) hxClAB
  -- Express the interior of the intersection in terms of the interiors.
  have hIntEq :
      interior (A ∩ B) = interior A ∩ interior B :=
    Topology.interior_inter_eq_inter (X := X) (A := A) (B := B)
  have hxNotIntInt : x ∉ interior A ∩ interior B := by
    intro hIntInt
    have : x ∈ interior (A ∩ B) := by
      simpa [hIntEq] using hIntInt
    exact hxNotIntAB this
  classical
  by_cases hIntA : x ∈ interior A
  · -- Then `x ∉ interior B`, hence `x` is in the boundary of `B`.
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      exact hxNotIntInt ⟨hIntA, hIntB⟩
    exact Or.inr ⟨hxClB, hNotIntB⟩
  · -- Otherwise, `x` is in the boundary of `A`.
    exact Or.inl ⟨hxClA, hIntA⟩

theorem Topology.interior_closure_congr_of_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A = closure B → interior (closure A) = interior (closure B) := by
  intro h
  simpa [h]

theorem Topology.closure_eq_univ_iff_interior_compl_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure A = (Set.univ : Set X) ↔ interior (Aᶜ) = (∅ : Set X) := by
  -- Useful relations between `closure` and `interior` for complements.
  have h₁ := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  have h₂ := Topology.closure_eq_compl_interior_compl (X := X) (A := A)
  constructor
  · intro hCl
    -- Rewrite `h₁` using `hCl` to eliminate `closure A`.
    have : interior (Aᶜ) = (Set.univ : Set X)ᶜ := by
      simpa [hCl] using h₁
    -- The complement of `univ` is `∅`.
    simpa [Set.compl_univ] using this
  · intro hInt
    -- Rewrite `h₂` using `hInt` to eliminate `interior (Aᶜ)`.
    have : closure A = (∅ : Set X)ᶜ := by
      simpa [hInt] using h₂
    -- The complement of `∅` is `univ`.
    simpa [Set.compl_empty] using this

theorem Topology.boundary_subset_closure_compl {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A ⊆ closure (Aᶜ) := by
  intro x hx
  rcases hx with ⟨hxClA, hxNotIntA⟩
  -- We verify the neighbourhood criterion for `x ∈ closure (Aᶜ)`.
  apply (mem_closure_iff).2
  intro V hVopen hxV
  -- Assume, for contradiction, that `V ∩ Aᶜ` is empty.
  by_contra hEmpty
  -- Then every point of `V` lies in `A`.
  have hSub : V ⊆ A := by
    intro y hyV
    by_contra hyNotA
    have : (V ∩ Aᶜ).Nonempty := ⟨y, ⟨hyV, hyNotA⟩⟩
    exact hEmpty this
  -- Hence `V` is an open neighbourhood of `x` contained in `A`,
  -- so `x ∈ interior A`, contradicting `hxNotIntA`.
  have : x ∈ interior A :=
    interior_maximal hSub hVopen hxV
  exact hxNotIntA this

theorem Topology.interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior B ⊆ interior (A ∪ B) := by
  exact interior_mono (Set.subset_union_right : B ⊆ A ∪ B)



theorem Topology.interior_closure_diff_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ closure A = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxInt, hxNotCl⟩
    have hxCl : x ∈ closure A := interior_subset hxInt
    exact (hxNotCl hxCl).elim
  · intro hx
    cases hx

theorem Topology.closure_union_closed_left {X : Type*} [TopologicalSpace X]
    {C A : Set X} (hC : IsClosed C) :
    closure (C ∪ A) = C ∪ closure A := by
  simpa [hC.closure_eq] using (closure_union C A)

theorem Topology.P3_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  -- First, translate `P3 A` into an openness condition using the closedness of `A`.
  have h₁ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  -- Next, characterize openness in terms of the interior for a closed set.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa [hOpen.interior_eq]
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences to obtain the desired statement.
  exact h₁.trans h₂

theorem Topology.interior_inter_boundary_eq_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∩ (closure A \ interior A) = (∅ : Set X) := by
  simpa using (Set.inter_diff_self (interior A) (closure A))

theorem Topology.closure_union_closure_compl_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases h : x ∈ closure A
    · exact Or.inl h
    · -- If `x ∉ closure A`, then `x` lies in the interior of `Aᶜ`,
      -- hence in `closure (Aᶜ)`.
      have hIntAcompl : x ∈ interior (Aᶜ) := by
        -- `interior (Aᶜ) = (closure A)ᶜ`.
        have h_eq :=
          Topology.interior_compl_eq_compl_closure (X := X) (A := A)
        have : x ∈ (closure A)ᶜ := by
          simpa using h
        simpa [h_eq] using this
      -- The interior is contained in the closure.
      have hClAcompl : x ∈ closure (Aᶜ) := by
        have : x ∈ (Aᶜ) := interior_subset hIntAcompl
        exact subset_closure this
      exact Or.inr hClAcompl

theorem Topology.boundary_union_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    ((closure A \ interior A) ∪ interior A) = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxbound => exact hxbound.1
    | inr hxInt   => exact subset_closure (interior_subset hxInt)
  · intro hxCl
    classical
    by_cases hxInt : x ∈ interior A
    · exact Or.inr hxInt
    · exact Or.inl ⟨hxCl, hxInt⟩

theorem Topology.nonempty_iff_nonempty_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    A.Nonempty ↔ (closure A).Nonempty := by
  classical
  constructor
  · intro hA
    exact hA.closure
  · intro hCl
    by_contra hA
    -- From `¬ A.Nonempty` obtain `A = ∅`.
    have hAempty : A = (∅ : Set X) :=
      (Set.not_nonempty_iff_eq_empty).1 hA
    -- Hence `closure A = ∅` by the existing characterization.
    have hClEmpty : closure A = (∅ : Set X) :=
      ((Topology.closure_eq_empty_iff (X := X) (A := A)).2 hAempty)
    -- But this contradicts the assumed non‐emptiness of `closure A`.
    rcases hCl with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := by
      simpa [hClEmpty] using hx
    cases this

theorem Topology.closure_interior_eq_univ_iff_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) ↔
      (Topology.P1 A ∧ closure A = Set.univ) := by
  constructor
  · intro h_cl_int
    have hP1 : Topology.P1 A :=
      Topology.P1_of_closure_interior_eq_univ (X := X) (A := A) h_cl_int
    have h_dense : closure A = (Set.univ : Set X) :=
      Topology.closure_eq_univ_of_closure_interior_eq_univ
        (X := X) (A := A) h_cl_int
    exact And.intro hP1 h_dense
  · rintro ⟨hP1, h_dense⟩
    exact
      Topology.closure_interior_eq_univ_of_P1
        (X := X) (A := A) hP1 h_dense

theorem Topology.boundary_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    closure A \ interior A ⊆ A := by
  intro x hx
  rcases hx with ⟨hxCl, _hxNotInt⟩
  simpa [hClosed.closure_eq] using hxCl

theorem Topology.closure_image_preimage_subset
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set Y) :
    closure (f '' (f ⁻¹' A)) ⊆ closure A := by
  -- First, prove the basic inclusion between the sets.
  have h_subset : f '' (f ⁻¹' A) ⊆ A := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_subset

theorem Topology.diff_closure_subset_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A \ closure B ⊆ interior (A \ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxNotClB⟩
  -- `interior A` is open, and so is the complement of `closure B`.
  have h_open₁ : IsOpen (interior A) := isOpen_interior
  have h_open₂ : IsOpen ((closure B)ᶜ) :=
    (isClosed_closure : IsClosed (closure B)).isOpen_compl
  let S : Set X := interior A ∩ (closure B)ᶜ
  have hS_open : IsOpen S := h_open₁.inter h_open₂
  have hxS : x ∈ S := And.intro hxIntA hxNotClB
  -- Show that `S ⊆ A \ B`.
  have h_subset : S ⊆ A \ B := by
    intro y hy
    rcases hy with ⟨hyIntA, hyNotClB⟩
    have hyA : y ∈ A := interior_subset hyIntA
    have hyNotB : y ∉ B := by
      intro hyB
      have : y ∈ closure B := subset_closure hyB
      exact hyNotClB this
    exact And.intro hyA hyNotB
  -- Apply the maximality property of the interior.
  have : x ∈ interior (A \ B) :=
    (interior_maximal h_subset hS_open) hxS
  exact this

theorem Topology.P2_interior_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P2 (interior (closure A) ∪ interior (closure B)) := by
  -- The union of two open sets is open.
  have h_open :
      IsOpen (interior (closure A) ∪ interior (closure B)) := by
    have hA : IsOpen (interior (closure A)) := isOpen_interior
    have hB : IsOpen (interior (closure B)) := isOpen_interior
    exact hA.union hB
  -- Open sets satisfy `P2`.
  exact
    Topology.isOpen_implies_P2
      (X := X)
      (A := interior (closure A) ∪ interior (closure B))
      h_open

theorem Topology.closure_interior_diff_interior_closure_subset_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ interior (closure A) ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxClIntA, hxNotIntClA⟩
  -- `x` lies in `closure A` because `interior A ⊆ A`.
  have hxClA : x ∈ closure A :=
    (Topology.closure_interior_subset_closure (X := X) (A := A)) hxClIntA
  -- Show that `x ∉ interior A`, otherwise we contradict `hxNotIntClA`.
  have hxNotIntA : x ∉ interior A := by
    intro hxIntA
    -- `interior A ⊆ interior (closure A)`, so `x` would be in the latter.
    have hxIntClA : x ∈ interior (closure A) :=
      (Topology.interior_subset_interior_closure (X := X) (A := A)) hxIntA
    exact hxNotIntClA hxIntClA
  exact And.intro hxClA hxNotIntA

theorem Topology.closure_inter_closure_compl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ closure (Aᶜ) = closure A \ interior A := by
  simpa using
    (Topology.closure_diff_interior_eq_closure_inter_closure_compl
        (X := X) (A := A)).symm

theorem Topology.closure_inter_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (closure A ∩ closure B) = closure A ∩ closure B := by
  have h_closed : IsClosed (closure A ∩ closure B) :=
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure B))
  simpa using h_closed.closure_eq

theorem Topology.interior_inter_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ∩ closure B ⊆ closure (A ∩ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxClB⟩
  -- We verify the neighbourhood criterion for `x ∈ closure (A ∩ B)`.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- Consider the neighbourhood `U ∩ interior A`, which is open and contains `x`.
  have hWopen : IsOpen (U ∩ interior A) := hUopen.inter isOpen_interior
  have hxW   : x ∈ U ∩ interior A := ⟨hxU, hxIntA⟩
  -- Since `x ∈ closure B`, this neighbourhood meets `B`.
  have h_nonempty : ((U ∩ interior A) ∩ B).Nonempty :=
    (mem_closure_iff).1 hxClB (U ∩ interior A) hWopen hxW
  -- Extract a witness lying in `U ∩ (A ∩ B)`.
  rcases h_nonempty with ⟨y, ⟨⟨hyU, hyIntA⟩, hyB⟩⟩
  have hyA : y ∈ A := interior_subset hyIntA
  exact ⟨y, ⟨hyU, ⟨hyA, hyB⟩⟩⟩

theorem Topology.closure_union_interior_subset_union_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) ⊆
      closure (interior A) ∪ closure (interior B) := by
  intro x hx
  -- Use the distributivity of `closure` over unions.
  have h :
      closure (interior A ∪ interior B) =
        closure (interior A) ∪ closure (interior B) := by
    simpa using closure_union (interior A) (interior B)
  -- Rewrite `hx` via the explicit equality and finish.
  simpa [h] using hx

theorem Topology.interior_diff_eq_diff_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  have hOpen : IsOpen (Bᶜ) := hB.isOpen_compl
  calc
    interior (A \ B) = interior (A ∩ Bᶜ) := by
      simpa [Set.diff_eq]
    _ = interior A ∩ Bᶜ := by
      simpa using
        Topology.interior_inter_open_right (X := X) (A := A) (U := Bᶜ) hOpen
    _ = interior A \ B := by
      simpa [Set.diff_eq, Set.inter_comm]

theorem Topology.interior_union_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = A ∪ B := by
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  simpa [hOpen.interior_eq]

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure A) hClosed)

theorem Topology.closure_eq_univ_of_closure_interior_eq_univ'
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · -- `closure A` is certainly contained in `univ`.
    intro _ _
    trivial
  · -- Use the hypothesis together with monotonicity of `closure`.
    have h_sub : closure (interior A) ⊆ closure A :=
      Topology.closure_interior_subset_closure (X := X) (A := A)
    simpa [h] using h_sub

theorem Topology.interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = Set.univ := by
  constructor
  · intro hInt
    apply Set.Subset.antisymm
    · exact Set.Subset_univ
    · intro x _
      -- Since `interior (closure A) = univ`, every point lies in this interior,
      -- hence in `closure A`.
      have hxInt : (x : X) ∈ interior (closure A) := by
        simpa [hInt] using (by simp : x ∈ (Set.univ : Set X))
      exact interior_subset hxInt
  · intro hCl
    exact
      Topology.interior_closure_eq_univ_of_dense
        (X := X) (A := A) hCl

theorem Set.inter_distrib_left {α : Type*} {s t u : Set α} :
    s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx_s, hxtu⟩
    cases hxtu with
    | inl hx_t => exact Or.inl ⟨hx_s, hx_t⟩
    | inr hx_u => exact Or.inr ⟨hx_s, hx_u⟩
  · intro hx
    cases hx with
    | inl hst => exact ⟨hst.1, Or.inl hst.2⟩
    | inr hsu => exact ⟨hsu.1, Or.inr hsu.2⟩

theorem Topology.closure_union_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A ∪ closure B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `A ⊆ A ∪ B`, so the monotonicity of `closure` yields the result.
      have h_subset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact h_subset hA
  | inr hB =>
      -- Symmetric argument for the second summand.
      have h_subset : closure B ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_right : B ⊆ A ∪ B)
      exact h_subset hB

theorem Topology.closure_union_closed_right {X : Type*} [TopologicalSpace X]
    {A C : Set X} (hC : IsClosed C) :
    closure (A ∪ C) = closure A ∪ C := by
  have h :=
    Topology.closure_union_closed_left (X := X) (C := C) (A := A) hC
  simpa [Set.union_comm] using h

theorem Topology.iUnion_interior_subset_interior_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, interior (A i)) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxInt⟩
  have h_subset :
      interior (A i) ⊆ interior (⋃ j, A j) :=
    interior_mono (Set.subset_iUnion (fun j ↦ A j) i)
  exact h_subset hxInt



theorem Topology.nonempty_of_nonempty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior A).Nonempty → A.Nonempty := by
  rintro ⟨x, hx⟩
  exact ⟨x, interior_subset hx⟩

theorem Topology.interior_inter_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∩ B) = A ∩ B := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa [hOpen.interior_eq]

theorem Topology.P1_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P1 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.isOpen_implies_P1 (X := X) (A := A ∩ B) hOpen

theorem Topology.closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  simpa [closure_closure] using
    (Topology.closure_inter_subset_inter_closure
      (X := X) (A := A) (B := closure B))

theorem Topology.P3_union_dense_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P3 (A ∪ B) := by
  -- First, show that `closure (A ∪ B) = univ`.
  have h_closure_union : closure (A ∪ B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · exact Set.Subset_univ
    · intro x _
      -- Since `closure A = univ`, every point lies in `closure A`.
      have hx_clA : (x : X) ∈ closure A := by
        simpa [h_dense]
      -- Monotonicity of `closure` gives the desired membership.
      have h_mono : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : A ⊆ A ∪ B)
      exact h_mono hx_clA
  -- Conclude using the criterion for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A ∪ B) h_closure_union

theorem Topology.P1_closure_iff_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure A) ↔ closure A = closure (interior (closure A)) := by
  -- Apply the general equivalence to the set `closure A`
  have h :=
    (Topology.P1_iff_closure_eq_closure_interior
      (X := X) (A := closure A))
  -- Rewrite `closure (closure A)` as `closure A`
  simpa [closure_closure] using h

theorem Topology.boundary_eq_empty_iff_open_and_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A = (∅ : Set X) ↔ (IsOpen A ∧ IsClosed A) := by
  classical
  constructor
  · intro h
    -- First show `closure A ⊆ interior A`.
    have h_subset : closure A ⊆ interior A := by
      intro x hx_cl
      by_cases hx_int : x ∈ interior A
      · exact hx_int
      ·
        -- Otherwise `x` would lie in the (empty) boundary.
        have h_mem : x ∈ closure A \ interior A := ⟨hx_cl, hx_int⟩
        have h_false : False := by
          have : x ∈ (∅ : Set X) := by
            simpa [h] using h_mem
          simpa using this
        exact (h_false.elim)
    -- Hence `interior A = A`.
    have h_int_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · intro x hxA
        exact h_subset (subset_closure hxA)
    -- And `closure A = A`.
    have h_cl_eq : closure A = A := by
      apply Set.Subset.antisymm
      · intro x hx_cl
        have : x ∈ interior A := h_subset hx_cl
        exact interior_subset this
      · exact subset_closure
    -- Conclude that `A` is both open and closed.
    have hOpen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [h_int_eq] using this
    have hClosed : IsClosed A := by
      have : IsClosed (closure A) := isClosed_closure
      simpa [h_cl_eq] using this
    exact And.intro hOpen hClosed
  · rintro ⟨hOpen, hClosed⟩
    -- For an open and closed set the boundary is empty.
    have h_int_eq : interior A = A := hOpen.interior_eq
    have h_cl_eq  : closure A = A  := hClosed.closure_eq
    simpa [h_int_eq, h_cl_eq, Set.diff_self]

theorem Topology.closure_union_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    closure (A ∪ B) = A ∪ B := by
  have hClosed : IsClosed (A ∪ B) := hA.union hB
  simpa using hClosed.closure_eq

theorem Topology.interior_closure_diff_interior_subset_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ interior A ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxIntCl, hxNotInt⟩
  have hxCl : x ∈ closure A := interior_subset hxIntCl
  exact And.intro hxCl hxNotInt

theorem Topology.closure_interior_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  have hxIntA : x ∈ closure (interior A) := by
    have h_subset : interior A ∩ B ⊆ interior A := Set.inter_subset_left
    exact (closure_mono h_subset) hx
  have hxB : x ∈ closure B := by
    have h_subset : interior A ∩ B ⊆ B := Set.inter_subset_right
    exact (closure_mono h_subset) hx
  exact And.intro hxIntA hxB

theorem Topology.interior_compl_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    interior (Aᶜ) = Aᶜ := by
  have h := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [hA.closure_eq] using h

theorem Topology.P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := closure A) hClosed)

theorem Topology.isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} : IsClosed (closure A ∩ closure B) := by
  simpa using
    (isClosed_closure : IsClosed (closure A)).inter
      (isClosed_closure : IsClosed (closure B))

theorem Topology.subset_interior_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : A ⊆ interior (closure A) := by
  simpa using
    (Topology.isOpen_implies_P3 (X := X) (A := A) hA)

theorem Topology.closure_preimage_closed_of_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {B : Set Y} (hB : IsClosed B) :
    closure (f ⁻¹' B) = f ⁻¹' B := by
  have hClosed : IsClosed (f ⁻¹' B) := hB.preimage hf
  simpa using hClosed.closure_eq

theorem Topology.P1_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P1 A := by
  -- A closed and dense set coincides with the whole space.
  have h_eq : A = (Set.univ : Set X) := by
    have h_cl : closure A = A := hClosed.closure_eq
    simpa [h_cl] using h_dense
  -- `P1` holds for `Set.univ`, hence for `A`.
  simpa [h_eq] using (Topology.P1_univ (X := X))

theorem Topology.closure_iInter_eq_iInter_of_isClosed
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, IsClosed (A i)) :
    closure (⋂ i, A i) = ⋂ i, A i := by
  classical
  have hClosed : IsClosed (⋂ i, A i) := isClosed_iInter hA
  simpa using hClosed.closure_eq

theorem Topology.closure_interior_inter_subset_closure_inter_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- First, observe that `interior (A ∩ B)` is contained in `interior A ∩ interior B`.
  have h_subset : interior (A ∩ B) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)) hx
    exact And.intro hxA hxB
  -- Taking closures preserves inclusions, giving the desired result.
  exact closure_mono h_subset

theorem Topology.nonempty_of_nonempty_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (interior (closure A)).Nonempty → A.Nonempty := by
  intro hInt
  rcases hInt with ⟨x, hxInt⟩
  -- `x` lies in the closure of `A`.
  have hxCl : (x : X) ∈ closure A := interior_subset hxInt
  -- If `A` were empty, its closure would also be empty, contradicting `hxCl`.
  by_cases hA : A.Nonempty
  · exact hA
  ·
    have hAempty : (A : Set X) = ∅ :=
      (Set.not_nonempty_iff_eq_empty).1 hA
    have : (x : X) ∈ (∅ : Set X) := by
      simpa [hAempty, closure_empty] using hxCl
    cases this

theorem Topology.closure_iInter_interiors_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, interior (A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- Show that `x` lies in each `closure (interior (A i))`.
  have hxi : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- The intersection of the interiors is contained in each individual interior.
    have h_subset : (⋂ j, interior (A j)) ⊆ interior (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` transfers the inclusion.
    have h_closure_subset :
        closure (⋂ j, interior (A j)) ⊆ closure (interior (A i)) :=
      closure_mono h_subset
    exact h_closure_subset hx
  -- Package the pointwise memberships into an intersection.
  exact Set.mem_iInter.2 hxi

theorem Topology.closure_interior_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ closure B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  -- `interior A ∩ closure B` is contained in `interior A`.
  have hx_left : x ∈ closure (interior A) := by
    have h_subset_left : interior A ∩ closure B ⊆ interior A :=
      Set.inter_subset_left
    exact (closure_mono h_subset_left) hx
  -- Likewise, `interior A ∩ closure B` is contained in `closure B`.
  have hx_right : x ∈ closure B := by
    have h_subset_right : interior A ∩ closure B ⊆ closure B := by
      intro y hy
      exact hy.2
    have : closure (interior A ∩ closure B) ⊆ closure (closure B) :=
      closure_mono h_subset_right
    simpa [closure_closure] using this hx
  exact And.intro hx_left hx_right

theorem Topology.interior_closure_union_closure_left_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (closure A ∪ B)) = interior (closure (A ∪ B)) := by
  have h :=
    Topology.closure_union_closure_left_eq_closure_union
      (X := X) (A := A) (B := B)
  simpa using congrArg (fun s : Set X => interior s) h

theorem Topology.interior_diff_open_left_eq_inter_interior_compl
    {X : Type*} [TopologicalSpace X] {U A : Set X} (hU : IsOpen U) :
    interior (U \ A) = U ∩ interior (Aᶜ) := by
  -- Step 1: rewrite `interior (U \ A)` using an existing lemma.
  have h₁ :=
    Topology.interior_diff_eq_diff_closure_of_isOpen
      (X := X) (A := U) (B := A) hU
  -- Step 2: express `interior (Aᶜ)` in terms of `closure A`.
  have h_int_compl :
      interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Step 3: chain the equalities to reach the desired identity.
  calc
    interior (U \ A)
        = U \ closure A := h₁
    _ = U ∩ (closure A)ᶜ := by
        simp [Set.diff_eq]
    _ = U ∩ interior (Aᶜ) := by
        simpa [h_int_compl]

theorem Topology.closure_interior_diff_closure_eq_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior A) \ closure A = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClInt, hxNotCl⟩
    have hxCl : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (X := X) (A := A)) hxClInt
    exact (hxNotCl hxCl).elim
  · intro hx
    cases hx



theorem Topology.boundary_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior A ⊆ closure A := by
  intro x hx
  exact hx.1

theorem Topology.interior_eq_closure_iff_open_and_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A = closure A ↔ (IsOpen A ∧ IsClosed A) := by
  constructor
  · intro h_eq
    -- First show `A = interior A`.
    have h_subset_int : (A : Set X) ⊆ interior A := by
      intro x hx
      have : (x : X) ∈ closure A := subset_closure hx
      simpa [h_eq] using this
    have h_int_eq : interior A = A := by
      apply Set.Subset.antisymm
      · exact interior_subset
      · exact h_subset_int
    -- Next show `A = closure A`.
    have h_cl_eq : closure A = A := by
      have : (closure A : Set X) = interior A := by
        simpa [h_eq]
      simpa [this, h_int_eq] using rfl
    -- Conclude that `A` is both open and closed.
    have h_open : IsOpen A := by
      simpa [h_int_eq] using (isOpen_interior : IsOpen (interior A))
    have h_closed : IsClosed A := by
      simpa [h_cl_eq] using (isClosed_closure : IsClosed (closure A))
    exact And.intro h_open h_closed
  · rintro ⟨h_open, h_closed⟩
    -- For an open and closed set, `interior` and `closure` coincide with the set itself.
    simpa [h_open.interior_eq, h_closed.closure_eq]

theorem Topology.P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ interior (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  dsimp [Topology.P3] at hP3
  exact hP3

theorem Set.inter_distrib_right {α : Type*} {s t u : Set α} :
    (t ∪ u) ∩ s = (t ∩ s) ∪ (u ∩ s) := by
  calc
    (t ∪ u) ∩ s = s ∩ (t ∪ u) := by
      simpa [Set.inter_comm]
    _ = (s ∩ t) ∪ (s ∩ u) := by
      simpa using (Set.inter_distrib_left (s := s) (t := t) (u := u))
    _ = (t ∩ s) ∪ (u ∩ s) := by
      simpa [Set.inter_comm, Set.inter_left_comm]

theorem Topology.closure_union_interior_subset_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure A ∪ interior B ⊆ closure (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      have h_subset : closure A ⊆ closure (A ∪ B) :=
        closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h_subset hxA
  | inr hxB =>
      -- `x` lies in `interior B`, hence in `B`, and therefore in `A ∪ B`.
      have hx_union : (x : X) ∈ A ∪ B := Or.inr (interior_subset hxB)
      -- Every point of `A ∪ B` belongs to its closure.
      exact subset_closure hx_union

theorem Topology.closure_diff_subset_boundary {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ A ⊆ closure A \ interior A := by
  intro x hx
  rcases hx with ⟨hxCl, hxNotA⟩
  have hxNotInt : x ∉ interior A := by
    intro hxInt
    exact hxNotA (interior_subset hxInt)
  exact And.intro hxCl hxNotInt

theorem Topology.P2_iff_P3_preimage_closed {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {A : Set Y}
    (hA : IsClosed A) :
    Topology.P2 (f ⁻¹' A) ↔ Topology.P3 (f ⁻¹' A) := by
  -- The preimage of a closed set under a continuous map is closed.
  have hClosed : IsClosed (f ⁻¹' A) := hA.preimage hf
  -- Apply the existing equivalence for closed sets.
  simpa using
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := f ⁻¹' A) hClosed)

theorem Topology.closure_subset_closure_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} : closure A ⊆ closure (A ∪ B) := by
  exact closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem Topology.closure_closure_inter_closed_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure (closure A ∩ B) = closure A ∩ B := by
  have hClosed : IsClosed (closure A ∩ B) :=
    (isClosed_closure : IsClosed (closure A)).inter hB
  simpa using hClosed.closure_eq

theorem Topology.closure_interior_inter_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact And.intro (subset_closure hx) hx

theorem Topology.isOpen_union_interior_compl_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : IsOpen (interior A ∪ (closure A)ᶜ) := by
  -- First, identify the set with the complement of the (closed) boundary.
  have h_eq :
      interior A ∪ (closure A)ᶜ =
        (closure A \ interior A)ᶜ := by
    simpa using
      (Topology.compl_boundary_eq_union_interior_compl_closure
        (X := X) (A := A)).symm
  -- The boundary `closure A \ interior A` is closed.
  have h_closed : IsClosed (closure A \ interior A) :=
    Topology.isClosed_closure_diff_interior (X := X) (A := A)
  -- Hence its complement is open.
  have h_open : IsOpen ((closure A \ interior A)ᶜ) :=
    h_closed.isOpen_compl
  simpa [h_eq] using h_open

theorem Topology.boundary_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) :
    closure A \ interior A ⊆ closure B := by
  intro x hx
  exact (closure_mono hAB) hx.1

theorem Topology.interior_preimage_open {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {A : Set Y}
    (hA : IsOpen A) :
    interior (f ⁻¹' A) = f ⁻¹' A := by
  have hOpen : IsOpen (f ⁻¹' A) := hA.preimage hf
  simpa [hOpen.interior_eq]

theorem Topology.closure_interior_subset_closed_iff {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure (interior A) ⊆ B ↔ interior A ⊆ B := by
  constructor
  · intro h_subset
    exact
      Set.Subset.trans
        (subset_closure : interior A ⊆ closure (interior A)) h_subset
  · intro h_int_subset
    exact closure_minimal h_int_subset hB

theorem Topology.interior_inter_closure_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ closure B) ⊆ interior A ∩ closure B := by
  intro x hx
  -- `hx` places `x` inside the interior of `A ∩ closure B`.
  have h_mem : x ∈ A ∩ closure B := interior_subset hx
  have hxClB : x ∈ closure B := h_mem.2
  -- Monotonicity of `interior` shows that `x` also lies in `interior A`.
  have hxIntA : x ∈ interior A := by
    have h_subset : interior (A ∩ closure B) ⊆ interior A :=
      interior_mono (Set.inter_subset_left : (A ∩ closure B) ⊆ A)
    exact h_subset hx
  exact And.intro hxIntA hxClB

theorem Topology.interior_inter_three_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) :
    interior (A ∩ B ∩ C) = A ∩ B ∩ C := by
  have hOpen : IsOpen (A ∩ B ∩ C) := (hA.inter hB).inter hC
  simpa using hOpen.interior_eq

theorem Topology.interior_closure_iterate_five_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- First, collapse the innermost three iterations using the idempotence lemma.
  have h₁ :=
    Topology.interior_closure_interior_closure_eq
      (X := X) (A := interior (closure A))
  -- Next, collapse the remaining two iterations in exactly the same way.
  have h₂ :=
    Topology.interior_closure_interior_closure_eq
      (X := X) (A := A)
  -- Chain the two equalities to obtain the desired result.
  simpa using h₁.trans h₂

theorem Topology.P2_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  exact Topology.isOpen_implies_P2 (X := X) (A := A ∩ B) hOpen

theorem Topology.closure_interior_union_eq_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∪ B) = closure (interior A) ∪ closure B := by
  simpa using closure_union (interior A) B

theorem Topology.P3_union_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 (interior A ∪ interior B) := by
  -- Both `interior A` and `interior B` are open,
  -- hence their union is open as well.
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union isOpen_interior
  -- Open sets satisfy `P3`.
  exact
    Topology.isOpen_implies_P3
      (X := X)
      (A := interior A ∪ interior B)
      h_open

theorem Topology.boundary_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) :
    closure A \ interior A ⊆ Aᶜ := by
  intro x hx
  -- `hx` provides `x ∈ closure A` and `x ∉ interior A`.
  -- Since `A` is open, `interior A = A`.
  have h_notA : x ∉ A := by
    have h_not_int : x ∉ interior A := hx.2
    simpa [hOpen.interior_eq] using h_not_int
  -- Membership in the complement is exactly the negation of membership in `A`.
  exact h_notA

theorem Topology.isOpen_implies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA
  have hP2 : Topology.P2 A :=
    Topology.isOpen_implies_P2 (X := X) (A := A) hA
  have hP3 : Topology.P3 A :=
    Topology.isOpen_implies_P3 (X := X) (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.closure_diff_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ A ⊆ closure (Aᶜ) := by
  intro x hx
  rcases hx with ⟨_, hxNotA⟩
  -- To show `x ∈ closure (Aᶜ)`, use the neighbourhood criterion.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- The point `x` itself witnesses the non‐emptiness of `U ∩ Aᶜ`.
  exact ⟨x, And.intro hxU hxNotA⟩

theorem Topology.boundary_eq_compl_interior_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    closure A \ interior A = (interior A)ᶜ := by
  calc
    closure A \ interior A
        = (Set.univ : Set X) \ interior A := by
          simpa [h_dense]
    _ = (interior A)ᶜ := by
          simpa [Set.diff_eq]

theorem Topology.closure_union_interiors_eq_union_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (interior A) (interior B)

theorem Topology.boundary_eq_closure_diff_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A \ interior A = closure A ∩ (interior A)ᶜ := by
  ext x
  simp [Set.diff_eq, Set.inter_comm]

theorem Topology.interior_diff_subset_diff_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B) ⊆ A \ closure B := by
  intro x hxInt
  -- From `hxInt` we know that `x ∈ A \ B`.
  have hxAB : x ∈ A ∧ x ∉ B := by
    have : x ∈ (A \ B) := interior_subset hxInt
    exact this
  have hxA : x ∈ A := hxAB.1
  -- We now show `x ∉ closure B`; otherwise we obtain a contradiction.
  have hxNotClB : x ∉ closure B := by
    intro hxClB
    -- Because `x ∈ interior (A \ B)`, the set `interior (A \ B)` is an open
    -- neighbourhood of `x` disjoint from `B`.
    have h_nonempty :=
      (mem_closure_iff).1 hxClB (interior (A \ B)) isOpen_interior hxInt
    rcases h_nonempty with ⟨y, ⟨hyInt, hyB⟩⟩
    -- But `hyInt : y ∈ interior (A \ B)` implies `y ∉ B`, contradicting `hyB`.
    have : y ∉ B := (interior_subset hyInt).2
    exact this hyB
  exact And.intro hxA hxNotClB

theorem Topology.boundary_empty {X : Type*} [TopologicalSpace X] :
    closure (∅ : Set X) \ interior (∅ : Set X) = (∅ : Set X) := by
  simp

theorem Topology.boundary_univ {X : Type*} [TopologicalSpace X] :
    closure (Set.univ : Set X) \ interior (Set.univ : Set X) = (∅ : Set X) := by
  simp

theorem Topology.interior_inter_interior_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (interior A ∩ interior B) = interior A ∩ interior B := by
  -- `interior A` is open, so we may apply `interior_inter_open_left`.
  have h_open : IsOpen (interior A) := isOpen_interior
  have h :=
    Topology.interior_inter_open_left
      (X := X) (U := interior A) (A := interior B) h_open
  -- Simplify `interior (interior B)` to `interior B`.
  simpa [interior_interior] using h

theorem Topology.nonempty_closure_of_nonempty_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty → (closure A).Nonempty := by
  intro h
  rcases h with ⟨x, hx⟩
  have h_subset : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (X := X) (A := A)
  exact ⟨x, h_subset hx⟩

theorem Topology.boundary_subset_closure_left {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior A ⊆ closure A := by
  intro x hx
  exact hx.1