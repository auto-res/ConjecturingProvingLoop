

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) :
    Topology.P1 A ∧ Topology.P3 A := by
  have hA : A ⊆ interior (closure (interior A)) := h
  have h1 : A ⊆ closure (interior A) :=
    Set.Subset.trans hA interior_subset
  have h2 : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have h3 : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h2
  have h4 : A ⊆ interior (closure A) :=
    Set.Subset.trans hA h3
  exact And.intro h1 h4

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ interior (closure A) := by
  simpa using interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem Topology.interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  exact interior_mono (closure_mono interior_subset)

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono hAB)

theorem Topology.isOpen_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 (X := X) A := by
  simpa [Topology.P3]
    using interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA

theorem Topology.isOpen_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 (X := X) A := by
  -- Using `P3` for open sets
  have h : A ⊆ interior (closure A) := Topology.isOpen_P3 (X := X) hA
  -- Rewrite the goal via `interior` of an open set
  simpa [Topology.P2, hA.interior_eq] using h

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using Topology.isOpen_P2 (X := X) (A := interior A) h_open

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (X := X) (interior A) := by
  dsimp [Topology.P3]
  have h : interior A ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      (Topology.interior_subset_interior_closure (X := X) (A := interior A))
  exact h

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior A) := by
  simpa [Topology.P1, interior_interior] using
    (subset_closure : (interior A : Set X) ⊆ closure (interior A))

theorem Topology.isOpen_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (X := X) A := by
  -- Obtain `P2` for the open set `A`
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_P2 (X := X) (A := A) hA
  -- From `P2` we immediately get `P1`
  exact (Topology.P2_implies_P1_and_P3 (X := X) (A := A) hP2).1

theorem Topology.P3_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (X := X) (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using Topology.isOpen_P3 (X := X) (A := interior (closure A)) h_open

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) :
    Topology.P3 (X := X) A := by
  exact (Topology.P2_implies_P1_and_P3 (X := X) (A := A) h).2

theorem Topology.P2_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using Topology.isOpen_P2 (X := X) (A := interior (closure A)) h_open

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior (closure A)) := by
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa using Topology.isOpen_P1 (X := X) (A := interior (closure A)) h_open

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) :
    Topology.P1 (X := X) A := by
  exact (Topology.P2_implies_P1_and_P3 (X := X) (A := A) h).1

theorem Topology.P1_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    Topology.isOpen_P1 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.closure_eq_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P1 (X := X) A) :
    closure (A : Set X) = closure (interior A) := by
  -- `closure (interior A)` is always a subset of `closure A`
  have h₁ : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono interior_subset
  -- From `P1` we have `A ⊆ closure (interior A)`
  have hA' : (A : Set X) ⊆ closure (interior A) := hA
  -- Taking closures gives the reverse inclusion
  have h₂ : closure (A : Set X) ⊆ closure (interior A) := by
    have : closure (A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA'
    simpa [closure_closure] using this
  exact Set.Subset.antisymm h₂ h₁

theorem Topology.P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) := by
  constructor
  · intro hA
    exact Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  · intro hEq
    have hsubset : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    simpa [Topology.P1, hEq] using hsubset

theorem Topology.interior_subset_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ interior (closure (interior A)) := by
  have h :
      interior (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
  simpa [interior_interior] using h

theorem Topology.P2_implies_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P2 (X := X) A) :
    closure (A : Set X) = closure (interior A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hA
  exact Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2
  · intro hP3
    simpa [Topology.P2, Topology.P3, hA.interior_eq] using hP3

theorem Topology.interior_closure_eq_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) = interior (closure (interior A)) := by
  have h_closure_eq : closure (A : Set X) = closure (interior A) :=
    Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hA
  simpa [h_closure_eq]

theorem Topology.interior_closure_eq_interior_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    interior (closure (A : Set X)) = interior (closure (interior A)) := by
  have h_closure_eq : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  simpa [h_closure_eq]

theorem Topology.P1_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (A ∪ B) := by
  -- Unfold the definition of `P1`
  dsimp [Topology.P1] at hA hB ⊢
  intro x hx
  -- Deal with the two cases coming from the union
  cases hx with
  | inl hxA =>
      -- From `P1` for `A`
      have hx_cl : x ∈ closure (interior A) := hA hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have h_sub : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        exact closure_mono h_int
      exact h_sub hx_cl
  | inr hxB =>
      -- From `P1` for `B`
      have hx_cl : x ∈ closure (interior B) := hB hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have h_sub : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        exact closure_mono h_int
      exact h_sub hx_cl

theorem Topology.P3_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  dsimp [Topology.P3] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure A) := hA hxA
      have h_sub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        exact interior_mono (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))
      exact h_sub hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure B) := hB hxB
      have h_sub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        exact interior_mono (closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))
      exact h_sub hx_int

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  constructor
  · intro _
    simpa using Topology.isOpen_P2 (X := X) (A := A) hA
  · intro _
    simpa using Topology.isOpen_P1 (X := X) (A := A) hA

theorem Topology.P2_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∪ B) := by
  -- Unfold `P2` for the given hypotheses and the goal.
  dsimp [Topology.P2] at hA hB ⊢
  intro x hx
  -- Analyse the membership of `x` in the union.
  cases hx with
  | inl hxA =>
      -- `x` satisfies the `P2` condition for `A`.
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- Show that the relevant neighbourhoods for `A`
      -- are contained in those for `A ∪ B`.
      have h_sub : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        -- Step 1: `interior A ⊆ interior (A ∪ B)`.
        have h1 : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        -- Step 2: take closures.
        have h2 : closure (interior A : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        -- Step 3: take interiors again.
        exact interior_mono h2
      exact h_sub hxA'
  | inr hxB =>
      -- Symmetric argument for the `B` branch.
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      have h_sub : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h1 : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        have h2 : closure (interior B : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h1
        exact interior_mono h2
      exact h_sub hxB'

theorem Topology.P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h1 : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h2 : Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  exact h1.trans h2

theorem Topology.P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) ∧
      Topology.P2 (X := X) (∅ : Set X) ∧
      Topology.P3 (X := X) (∅ : Set X) := by
  have h1 : Topology.P1 (X := X) (∅ : Set X) := by
    dsimp [Topology.P1]
    simp
  have h2 : Topology.P2 (X := X) (∅ : Set X) := by
    dsimp [Topology.P2]
    simp
  have h3 : Topology.P3 (X := X) (∅ : Set X) := by
    dsimp [Topology.P3]
    simp
  exact And.intro h1 (And.intro h2 h3)

theorem Topology.P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) ∧
      Topology.P2 (X := X) (Set.univ : Set X) ∧
      Topology.P3 (X := X) (Set.univ : Set X) := by
  have h₁ : Topology.P1 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P1]
    simp
  have h₂ : Topology.P2 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P2]
    simp
  have h₃ : Topology.P3 (X := X) (Set.univ : Set X) := by
    dsimp [Topology.P3]
    simp
  exact And.intro h₁ (And.intro h₂ h₃)

theorem Topology.P2_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    Topology.isOpen_P2 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.P3_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (X := X) (interior (closure (interior A))) := by
  have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
  simpa using
    Topology.isOpen_P3 (X := X) (A := interior (closure (interior A))) h_open

theorem Topology.P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (A : Set X) = Set.univ) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hx
  have h_int : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hA, interior_univ]
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_int] using hx_univ

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  exact interior_mono (closure_mono hAB)

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- First enlarge `interior A` to `interior B` using monotonicity of `interior`.
  have h₁ : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Then enlarge the closures accordingly.
  have h₂ : closure (interior A : Set X) ⊆ closure (interior B) :=
    closure_mono h₁
  -- Finally, take interiors once more to get the desired inclusion.
  exact interior_mono h₂

theorem Topology.P1_iUnion {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, Topology.P1 (X := X) (A i)) :
    Topology.P1 (X := X) (⋃ i, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Obtain an index witnessing `x ∈ A i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- From `P1` for `A i`.
  have hx_cl : x ∈ closure (interior (A i)) := hA i hxAi
  -- Show that this closure is contained in the desired one.
  have h_sub : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    -- First, relate the interiors.
    have h_int : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      -- `A i ⊆ ⋃ j, A j`.
      have h_union : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_union
    -- Then, take closures.
    exact closure_mono h_int
  exact h_sub hx_cl

theorem Topology.P2_iUnion {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, Topology.P2 (X := X) (A i)) :
    Topology.P2 (X := X) (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  -- Choose an index `i` such that `x ∈ A i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Apply `P2` for the chosen `i`.
  have hx_int : x ∈ interior (closure (interior (A i))) := hA i hxAi
  -- Show that the relevant neighbourhood for `A i`
  -- is contained in the corresponding one for the union.
  have h_sub : interior (closure (interior (A i))) ⊆
      interior (closure (interior (⋃ j, A j))) := by
    -- Step 1: `interior (A i) ⊆ interior (⋃ j, A j)`.
    have h1 : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      have h_union : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_union
    -- Step 2: take closures.
    have h2 : closure (interior (A i) : Set X) ⊆ closure (interior (⋃ j, A j)) :=
      closure_mono h1
    -- Step 3: take interiors again.
    exact interior_mono h2
  -- Finish the proof.
  exact h_sub hx_int

theorem Topology.P3_iUnion {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, Topology.P3 (X := X) (A i)) :
    Topology.P3 (X := X) (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx_int : x ∈ interior (closure (A i)) := hA i hxAi
  have h_sub : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have h_set : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    have h_closure : closure (A i : Set X) ⊆ closure (⋃ j, A j) :=
      closure_mono h_set
    exact interior_mono h_closure
  exact h_sub hx_int

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) := by
  dsimp [Topology.P1]
  simp

theorem Topology.interior_closure_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  simpa using
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))

theorem Topology.interior_closure_inter_subset_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `x` lies in the interior of `closure A`
  have hxA : x ∈ interior (closure A) := by
    -- First, enlarge `closure (A ∩ B)` to `closure A`
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    -- Then, pass to interiors
    have h₂ : interior (closure (A ∩ B : Set X)) ⊆ interior (closure A) :=
      interior_mono h₁
    exact h₂ hx
  -- `x` lies in the interior of `closure B`
  have hxB : x ∈ interior (closure B) := by
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    have h₂ : interior (closure (A ∩ B : Set X)) ⊆ interior (closure B) :=
      interior_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP3
    -- `A ⊆ interior (closure A)` and `closure A = A` yield `A ⊆ interior A`.
    have h_sub : (A : Set X) ⊆ interior A := by
      dsimp [Topology.P3] at hP3
      simpa [h_closed.closure_eq] using hP3
    -- Together with `interior A ⊆ A` we get equality.
    have h_eq : interior (A : Set X) = A :=
      Set.Subset.antisymm interior_subset h_sub
    -- An equality with an open set yields openness of `A`.
    have h_open : IsOpen (A : Set X) := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_eq] using this
    exact h_open
  · intro h_open
    exact Topology.isOpen_P3 (X := X) (A := A) h_open

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1]  -- unfold the goal
  intro x hx
  -- From `P3` we know `A ⊆ interior (closure A)`.
  have h_subset : (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
    have hA_sub : (A : Set X) ⊆ interior (closure A) := hA
    exact closure_mono hA_sub
  exact h_subset hx

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (X := X) A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    exact
      (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP3
  · intro h_open
    exact Topology.isOpen_P2 (X := X) (A := A) h_open

theorem Topology.P1_sUnion {X : Type*} [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ A : Set X, A ∈ F → Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (⋃₀ F) := by
  dsimp [Topology.P1] at hF ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAF, hxA⟩
  -- Apply `P1` for the witnessing set `A`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hF A hAF hxA
  -- Show that the relevant closure for `A` is contained in that for `⋃₀ F`.
  have h_int : (interior (A : Set X)) ⊆ interior (⋃₀ F) := by
    have h_subset : (A : Set X) ⊆ ⋃₀ F := Set.subset_sUnion_of_mem hAF
    exact interior_mono h_subset
  have h_sub : closure (interior (A : Set X)) ⊆ closure (interior (⋃₀ F)) :=
    closure_mono h_int
  exact h_sub hx_cl

theorem Topology.P3_sUnion {X : Type*} [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ A : Set X, A ∈ F → Topology.P3 (X := X) A) :
    Topology.P3 (X := X) (⋃₀ F) := by
  dsimp [Topology.P3] at hF ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAF, hxA⟩
  have hx_int : x ∈ interior (closure A) := hF A hAF hxA
  have h_subset : interior (closure A) ⊆ interior (closure (⋃₀ F)) := by
    have h_set : (A : Set X) ⊆ ⋃₀ F :=
      Set.subset_sUnion_of_mem hAF
    have h_closure : closure (A : Set X) ⊆ closure (⋃₀ F) :=
      closure_mono h_set
    exact interior_mono h_closure
  exact h_subset hx_int

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    Topology.P1 (X := X) (closure A) := by
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  exact Topology.P3_implies_P1_closure (X := X) (A := A) hP3

theorem Topology.P1_iff_closure_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) A ↔ closure (interior A) = (A : Set X) := by
  -- Start from the general characterization of `P1`.
  have h_equiv := Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  -- Since `A` is closed, `closure A = A`; rewrite and use symmetry of equality.
  simpa [h_closed.closure_eq, eq_comm] using h_equiv

theorem Topology.P2_sUnion {X : Type*} [TopologicalSpace X] (F : Set (Set X))
    (hF : ∀ A : Set X, A ∈ F → Topology.P2 (X := X) A) :
    Topology.P2 (X := X) (⋃₀ F) := by
  dsimp [Topology.P2] at hF ⊢
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAF, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := hF A hAF hxA
  have h_sub : interior (closure (interior A)) ⊆
      interior (closure (interior (⋃₀ F))) := by
    -- Step 1: relate the interiors.
    have h1 : (interior A : Set X) ⊆ interior (⋃₀ F) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ F := Set.subset_sUnion_of_mem hAF
      exact interior_mono hA_subset
    -- Step 2: take closures of both sides.
    have h2 : closure (interior A : Set X) ⊆ closure (interior (⋃₀ F)) :=
      closure_mono h1
    -- Step 3: take interiors again.
    exact interior_mono h2
  exact h_sub hx_int

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h1 : Topology.P2 (X := X) A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA
  have h2 : Topology.P3 (X := X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  exact h1.trans h2.symm

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- Use monotonicity with the inclusion `A ⊆ A ∪ B`.
      have h_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        Topology.interior_closure_interior_mono
          (X := X) (A := A) (B := A ∪ B) (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h_subset hA
  | inr hB =>
      -- Symmetric argument for the `B` component.
      have h_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        Topology.interior_closure_interior_mono
          (X := X) (A := B) (B := A ∪ B) (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h_subset hB

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (A : Set X) := by
  -- First, `interior (closure (interior A))` is contained in `closure (interior A)`.
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- Next, `closure (interior A)` is contained in `closure A`.
  have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono interior_subset
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Topology.interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Use the equality of closures obtained from `P1`.
  have h_cl : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  -- Reinterpret `hx` via this equality.
  have hx' : x ∈ closure (interior A) := by
    simpa [h_cl] using hx
  -- Relate the two closures through monotonicity.
  have h_incl : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- Since `interior A ⊆ interior (closure A)` ...
    have h_subset : (interior A : Set X) ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (X := X) (A := A)
    -- ... taking closures yields the desired inclusion.
    exact closure_mono h_subset
  exact h_incl hx'

theorem Topology.interior_closure_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure (B : Set X)) ⊆
      interior (closure (A ∪ B : Set X)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `A` branch
      have h_sub : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        -- `closure A ⊆ closure (A ∪ B)`
        have h_cl : (closure (A : Set X)) ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
        -- Take interiors
        exact interior_mono h_cl
      exact h_sub hA
  | inr hB =>
      -- `B` branch
      have h_sub : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        -- `closure B ⊆ closure (A ∪ B)`
        have h_cl : (closure (B : Set X)) ⊆ closure (A ∪ B) :=
          closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
        -- Take interiors
        exact interior_mono h_cl
      exact h_sub hB



theorem Topology.interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure A) := by
  -- We show the two inclusions separately.
  apply Set.Subset.antisymm
  · -- First inclusion: `⊆`
    have h_cl :
        closure (interior (closure (A : Set X))) ⊆ closure A := by
      -- `interior (closure A) ⊆ closure A`
      have h₁ : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
        interior_subset
      -- Taking closures preserves this inclusion.
      have h₂ :
          closure (interior (closure (A : Set X))) ⊆
            closure (closure (A : Set X)) :=
        closure_mono h₁
      simpa [closure_closure] using h₂
    -- Monotonicity of `interior` yields the desired inclusion.
    exact interior_mono h_cl
  · -- Second inclusion: `⊇`
    -- `interior (closure A)` is open.
    have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- It is contained in `closure (interior (closure A))`.
    have h_sub :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) :=
      subset_closure
    -- An open set contained in a set lies in its interior.
    have h_incl :
        interior (closure (A : Set X)) ⊆
          interior (closure (interior (closure (A : Set X)))) :=
      interior_maximal h_sub h_open
    exact h_incl

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- We will show that `closure (interior A)` is contained in
  -- `closure (interior (closure (interior A)))`.
  have h_sub :
      closure (interior A : Set X) ⊆
        closure (interior (closure (interior A))) := by
    -- First, `interior A ⊆ interior (closure (interior A))`.
    have h₁ :
        (interior A : Set X) ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using
        (Topology.interior_subset_interior_closure
          (X := X) (A := interior A))
    -- Taking closures preserves this inclusion.
    exact closure_mono h₁
  exact h_sub hx

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (closure A)) := by
  -- `interior A` is contained in `interior (closure A)` by monotonicity of `interior`.
  have h : (interior (A : Set X)) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Taking closures of both sides yields the desired inclusion.
  exact closure_mono h

theorem Topology.interior_closure_interior_inter_subset_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A ∩ B : Set X))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hxA : x ∈ interior (closure (interior A)) := by
    -- `A ∩ B ⊆ A`
    have h₁ : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    -- `interior (A ∩ B) ⊆ interior A`
    have h₂ : (interior (A ∩ B : Set X) : Set X) ⊆ interior A :=
      interior_mono h₁
    -- `closure (interior (A ∩ B)) ⊆ closure (interior A)`
    have h₃ : closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) :=
      closure_mono h₂
    -- Taking interiors yields the desired inclusion
    have h₄ :
        interior (closure (interior (A ∩ B : Set X))) ⊆
          interior (closure (interior A)) :=
      interior_mono h₃
    exact h₄ hx
  have hxB : x ∈ interior (closure (interior B)) := by
    -- `A ∩ B ⊆ B`
    have h₁ : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    -- `interior (A ∩ B) ⊆ interior B`
    have h₂ : (interior (A ∩ B : Set X) : Set X) ⊆ interior B :=
      interior_mono h₁
    -- `closure (interior (A ∩ B)) ⊆ closure (interior B)`
    have h₃ : closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) :=
      closure_mono h₂
    -- Taking interiors yields the desired inclusion
    have h₄ :
        interior (closure (interior (A ∩ B : Set X))) ⊆
          interior (closure (interior B)) :=
      interior_mono h₃
    exact h₄ hx
  exact And.intro hxA hxB

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔
      (Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) := by
  constructor
  · intro hP1
    -- Derive `P2` from `P1` using the equivalence for open sets.
    have hP2 : Topology.P2 (X := X) A :=
      (Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA).1 hP1
    -- Derive `P3` from `P1` using the corresponding equivalence.
    have hP3 : Topology.P3 (X := X) A :=
      (Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA).1 hP1
    exact And.intro hP2 hP3
  · intro h
    -- From `P2` we can always deduce `P1`.
    exact Topology.P2_implies_P1 (X := X) (A := A) h.1

theorem Topology.P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A : Set X) = Set.univ) :
    Topology.P2 (X := X) A := by
  dsimp [Topology.P2]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hA, interior_univ] using this

theorem Topology.closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    closure (A : Set X) = closure (interior (closure A)) := by
  -- From `P3` for `A` we get `P1` for `closure A`.
  have hP1 : Topology.P1 (X := X) (closure A) :=
    Topology.P3_implies_P1_closure (X := X) (A := A) hA
  -- Apply the equality obtained from `P1`.
  have hEq :
      closure (closure (A : Set X)) = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := closure A) hP1
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hEq

theorem Topology.P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A : Set X) = Set.univ) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [hA] using this

theorem Topology.closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- Handle the case `x ∈ closure (interior A)`.
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        -- Since `A ⊆ A ∪ B`, their interiors satisfy the same inclusion.
        have h_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        -- Taking closures preserves the inclusion.
        exact closure_mono h_int
      exact h_sub hA
  | inr hB =>
      -- Symmetric argument for the case `x ∈ closure (interior B)`.
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        exact closure_mono h_int
      exact h_sub hB

theorem Topology.closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  · -- `closure (interior (closure (interior A))) ⊆ closure (interior A)`
    have h₁ :
        (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `closure (interior A) ⊆ closure (interior (closure (interior A)))`
    have h :
        closure (interior A : Set X) ⊆
          closure (interior (closure (interior A))) := by
      simpa [interior_interior] using
        (Topology.closure_interior_subset_closure_interior_closure
          (X := X) (A := interior A))
    exact h

theorem Topology.closure_interior_closure_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  -- We establish the two inclusions separately and conclude by antisymmetry.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    have h1 :
        interior (closure (interior (closure (A : Set X)))) ⊆
          closure (interior (closure (A : Set X))) := by
      -- An interior is always contained in the set it is taken from.
      simpa using
        (interior_subset :
          interior (closure (interior (closure (A : Set X)))) ⊆
            closure (interior (closure (A : Set X))))
    -- Taking closures preserves inclusion; `closure (closure _)` simplifies.
    simpa [closure_closure] using closure_mono h1
  · -- `⊇` direction
    have h2 :
        closure (interior (closure (A : Set X))) ⊆
          closure (interior (closure (interior (closure (A : Set X))))) := by
      -- Use the generic monotonicity lemma with `A := interior (closure A)`.
      have h :
          closure (interior (interior (closure (A : Set X)))) ⊆
            closure (interior (closure (interior (closure (A : Set X))))) :=
        Topology.closure_interior_subset_closure_interior_closure
          (X := X) (A := interior (closure (A : Set X)))
      simpa [interior_interior] using h
    exact h2

theorem Topology.closure_interior_inter_subset_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show membership in `closure (interior A)`
  have hxA : x ∈ closure (interior A) := by
    -- `A ∩ B ⊆ A`
    have h_subset_AB_A : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    -- Then `interior (A ∩ B) ⊆ interior A`
    have h_int : (interior (A ∩ B : Set X) : Set X) ⊆ interior A :=
      interior_mono h_subset_AB_A
    -- Taking closures preserves inclusion
    have h_closure : closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) :=
      closure_mono h_int
    exact h_closure hx
  -- Show membership in `closure (interior B)`
  have hxB : x ∈ closure (interior B) := by
    -- `A ∩ B ⊆ B`
    have h_subset_AB_B : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    -- Then `interior (A ∩ B) ⊆ interior B`
    have h_int : (interior (A ∩ B : Set X) : Set X) ⊆ interior B :=
      interior_mono h_subset_AB_B
    -- Taking closures preserves inclusion
    have h_closure : closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) :=
      closure_mono h_int
    exact h_closure hx
  exact And.intro hxA hxB

theorem Topology.P2_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure A) h_closed)

theorem Topology.interior_closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (A : Set X))))) =
      interior (closure (interior A)) := by
  -- We establish the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    -- Step 1: `interior (closure (interior A)) ⊆ closure (interior A)`.
    have h₁ :
        (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    -- Step 2: take closures of both sides.
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    -- Step 3: simplify the right‐hand side.
    have h₂' :
        closure (interior (closure (interior A))) ⊆
          closure (interior A) := by
      simpa [closure_closure] using h₂
    -- Step 4: take interiors once more.
    exact interior_mono h₂'
  · -- `⊇` direction
    -- The set `interior (closure (interior A))` is open.
    have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
    -- It is contained in its own closure, hence in the larger closure that appears.
    have h_subset :
        (interior (closure (interior A)) : Set X) ⊆
          closure (interior (closure (interior (A : Set X)))) := by
      simpa using
        (subset_closure :
          (interior (closure (interior A)) : Set X) ⊆
            closure (interior (closure (interior A))))
    -- Apply maximality of the interior for an open set.
    have h_incl :
        interior (closure (interior A)) ⊆
          interior (closure (interior (closure (interior A)))) :=
      interior_maximal h_subset h_open
    -- Conclude the desired inclusion.
    simpa using h_incl

theorem Topology.closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure A := by
  -- `interior (closure A)` is contained in `closure A`.
  have h₁ :
      (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
    interior_subset
  -- Taking closures preserves the inclusion.
  have h₂ :
      closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
    closure_mono h₁
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h₂

theorem Topology.interior_closure_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure A := by
  exact interior_subset

theorem Topology.P2_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ interior (A : Set X) = A := by
  -- First, recall that for a closed set `A`, `P2 A` is equivalent to `A` being open.
  have h_equiv := Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) h_closed
  constructor
  · intro hP2
    -- From `P2` and the equivalence we get that `A` is open,
    -- hence `interior A = A`.
    have h_open : IsOpen (A : Set X) := h_equiv.mp hP2
    simpa using h_open.interior_eq
  · intro h_int
    -- From the equality `interior A = A` we deduce that `A` is open,
    -- and hence `P2 A` holds by the equivalence.
    have h_open : IsOpen (A : Set X) := by
      simpa [h_int] using
        (isOpen_interior : IsOpen (interior (A : Set X)))
    exact h_equiv.mpr h_open

theorem Topology.P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) ↔ IsOpen (closure A) := by
  have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := closure A) h_closed)

theorem Topology.interior_closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆ closure A := by
  simpa [closure_closure] using
    (Topology.interior_closure_interior_subset_closure
      (X := X) (A := closure A))

theorem Topology.closure_interior_iter_three_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
        closure (interior (closure (interior A))) := by
          simpa using
            Topology.closure_interior_closure_interior_eq
              (X := X) (A := closure (interior A))
    _ = closure (interior A) := by
          simpa using
            Topology.closure_interior_closure_interior_eq
              (X := X) (A := A)

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) ↔ Topology.P3 (X := X) (closure A) := by
  have h₁ : Topology.P2 (X := X) (closure A) ↔ IsOpen (closure A) :=
    Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  have h₂ : Topology.P3 (X := X) (closure A) ↔ IsOpen (closure A) :=
    Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)
  exact h₁.trans h₂.symm

theorem Topology.interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
      interior (closure (interior A)) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
        interior (closure (interior (closure (interior A)))) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := closure (interior (A : Set X))))
    _ = interior (closure (interior A)) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := A))

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- Use the idempotence lemma to rewrite the target set.
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq
        (X := X) (A := closure A))
  -- The goal follows by rewriting with `h_eq`.
  simpa [h_eq] using hx

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  exact
    Set.Subset.trans
      (Topology.interior_closure_interior_subset_closure_interior
        (X := X) (A := A))
      (Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A))

theorem Topology.closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure A := by
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem Topology.P1_P2_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.isOpen_P1 (X := X) (A := A) hA
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_P2 (X := X) (A := A) hA
  have hP3 : Topology.P3 (X := X) A :=
    Topology.isOpen_P3 (X := X) (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.interior_closure_subset_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  -- From `P2` we know the closures of `A` and `interior A` coincide.
  have hEq : closure (A : Set X) = closure (interior A) :=
    Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hA
  -- Rewrite the source set using this equality.
  have hIntEq :
      interior (closure (A : Set X)) = interior (closure (interior A)) := by
    simpa [hEq]
  -- Establish the desired inclusion.
  intro x hx
  -- Transport membership via the rewritten equality.
  have hx' : x ∈ interior (closure (interior A)) := by
    simpa [hIntEq] using hx
  -- The interior is always contained in the set it is taken from.
  exact
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) hx'

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A : Set X) = Set.univ) :
    Topology.P3 (X := X) A := by
  -- First, show that `closure A = univ`.
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is always contained in `closure A`.
    have h_subset : closure (interior A : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- Hence `univ ⊆ closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [hA] using h_subset
    -- The reverse inclusion holds trivially.
    have h_closure_subset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx; simp
    -- Combine the two inclusions to get the desired equality.
    exact Set.Subset.antisymm h_closure_subset h_univ_subset
  -- Conclude by applying the existing lemma for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A) h_closure_univ

theorem Topology.interior_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure (interior (closure A)) := by
  simpa using
    (subset_closure :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure A)))

theorem Topology.interior_closure_eq_interior_closure_interior_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure A))) := by
  -- `P3` for `A` gives `P1` for `closure A`.
  have hP1 : Topology.P1 (X := X) (closure A) :=
    Topology.P3_implies_P1_closure (X := X) (A := A) hA
  -- Apply the existing equality for `P1`.
  have h_eq :
      interior (closure (closure (A : Set X))) =
        interior (closure (interior (closure A))) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1
      (X := X) (A := closure A) hP1
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h_eq

theorem Topology.P1_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hB : B ⊆ closure (interior A)) :
    Topology.P1 (X := X) B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` is in `closure (interior A)` by `hB`.
  have hx_closureA : x ∈ closure (interior A) := hB hxB
  -- From `A ⊆ B` we deduce `interior A ⊆ interior B`.
  have h_int : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Taking closures yields the required inclusion.
  have h_closure : closure (interior A : Set X) ⊆ closure (interior B) :=
    closure_mono h_int
  -- Conclude that `x` is in `closure (interior B)`.
  exact h_closure hx_closureA

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1, Topology.P3] at *
  intro x hxA
  -- From `P3`, `x` lies in the interior of `closure A`.
  have hx_int_closure : x ∈ interior (closure A) := hP3 hxA
  -- Since `A` is closed, `closure A = A`.
  have h_closure_eq : closure (A : Set X) = A := h_closed.closure_eq
  -- Hence `x` actually lies in `interior A`.
  have hx_int : x ∈ interior A := by
    simpa [h_closure_eq] using hx_int_closure
  -- The interior of a set is always contained in the closure of the interior.
  have h_subset : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  exact h_subset hx_int

theorem Topology.closure_interior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (interior A) = closure (A : Set X) := by
  simpa [hA.interior_eq]

theorem Topology.open_subset_closure_iff_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A U : Set X} (hU : IsOpen (U : Set X)) :
    (U ⊆ closure (A : Set X)) ↔ U ⊆ interior (closure A) := by
  constructor
  · intro hU_sub
    exact interior_maximal hU_sub hU
  · intro hU_sub
    exact Set.Subset.trans hU_sub interior_subset

theorem Topology.P3_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ interior (A : Set X) = A := by
  -- First, recall that for a closed set `A`, `P3 A` is equivalent to `A` being open.
  have h1 : Topology.P3 (X := X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed
  -- For any set, being open is equivalent to coinciding with its interior.
  have h2 : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro h_open
      simpa using h_open.interior_eq
    · intro h_int_eq
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_int_eq] using this
  -- Combine the two equivalences.
  exact h1.trans h2

theorem Topology.interior_closure_eq_self_of_isClosed_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  simpa [h_closed.closure_eq, h_open.interior_eq]

theorem Topology.P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) :
    Topology.P2 (X := X) (A ∪ B ∪ C) := by
  -- First combine `A` and `B`.
  have hAB : Topology.P2 (X := X) (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Then union the result with `C`.
  have hABC : Topology.P2 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC

theorem Topology.P1_P2_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) hA
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) hA
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P3_of_dense_interior (X := X) (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P3 (X := X) A) (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C) :
    Topology.P3 (X := X) (A ∪ B ∪ C) := by
  -- First, union `A` and `B`.
  have hAB : Topology.P3 (X := X) (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P3 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC

theorem Topology.closure_interior_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior (A : Set X))) = closure (interior A) := by
  simpa [interior_interior]

theorem Topology.P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) :
    Topology.P1 (X := X) (A ∪ B ∪ C) := by
  -- First, combine `A` and `B`.
  have hAB : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Then, union the result with `C`.
  have hABC : Topology.P1 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P1_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
  -- Rewrite via associativity of union.
  simpa [Set.union_assoc] using hABC

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure A)) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3] at h ⊢
  intro x hxA
  -- From `x ∈ A` we know `x ∈ closure A`.
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  -- Apply `P3` for `closure A`.
  have hx_int : x ∈ interior (closure (closure A)) := h hx_cl
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using hx_int

theorem Topology.interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      have h_subset : (interior (A : Set X)) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
      exact h_subset hA
  | inr hB =>
      have h_subset : (interior (B : Set X)) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
      exact h_subset hB

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (closure A)) :
    Topology.P3 (X := X) A := by
  -- First, convert `P2 (closure A)` to `P3 (closure A)`.
  have hP3Closure : Topology.P3 (X := X) (closure A) :=
    (Topology.P2_closure_iff_P3_closure (X := X) (A := A)).1 h
  -- Then, descend from `closure A` to `A`.
  exact Topology.P3_of_P3_closure (X := X) (A := A) hP3Closure

theorem Topology.P3_union_of_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Upgrade the `P2` hypotheses to `P3`.
  have hA3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  have hB3 : Topology.P3 (X := X) B :=
    Topology.P2_implies_P3 (X := X) (A := B) hB
  -- Apply the union lemma for `P3`.
  exact Topology.P3_union (X := X) (A := A) (B := B) hA3 hB3

theorem Topology.closure_interior_iInter_subset
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (interior (⋂ i, A i : Set X)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- We will show that `x` belongs to each `closure (interior (A i))`.
  have hx_each : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- First, note that `⋂ i, A i ⊆ A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      -- Expand the intersection membership.
      have h_all : ∀ j, y ∈ A j := (Set.mem_iInter.mp hy)
      exact h_all i
    -- Monotonicity of `interior` gives the corresponding inclusion for interiors.
    have h_int :
        (interior (⋂ j, A j : Set X) : Set X) ⊆ interior (A i) :=
      interior_mono h_subset
    -- Taking closures preserves inclusion.
    have h_closure :
        closure (interior (⋂ j, A j : Set X)) ⊆ closure (interior (A i)) :=
      closure_mono h_int
    -- Apply the inclusion to the hypothesis.
    exact h_closure hx
  -- Combine the pointwise memberships into one for the intersection.
  exact (Set.mem_iInter.2 hx_each)

theorem Topology.interior_closure_interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure B) := by
  -- First, `interior A ⊆ B` because `interior A ⊆ A` and `A ⊆ B`.
  have h₁ : (interior A : Set X) ⊆ B := by
    intro x hx
    exact hAB (interior_subset hx)
  -- Taking closures preserves this inclusion.
  have h₂ : closure (interior A : Set X) ⊆ closure B := closure_mono h₁
  -- Taking interiors once more yields the desired inclusion.
  exact interior_mono h₂

theorem Topology.closure_interior_iter_four_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))) =
        closure (interior (closure (interior (A : Set X)))) := by
          simpa using
            Topology.closure_interior_iter_three_eq
              (X := X) (A := closure (interior A))
    _ = closure (interior A) := by
          simpa using
            Topology.closure_interior_closure_interior_eq
              (X := X) (A := A)

theorem Topology.interior_closure_interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- The required inclusion follows from monotonicity with
  -- respect to the evident inclusion `A ⊆ closure A`.
  have h_mono :=
    Topology.interior_closure_interior_mono
      (X := X) (A := A) (B := closure A) (subset_closure : (A : Set X) ⊆ closure A)
  simpa using h_mono

theorem Topology.interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (∅ : Set X) ↔ interior (A : Set X) = ∅ := by
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`,
    -- hence is empty if the latter is.
    have hsubset :
        interior (A : Set X) ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interior_closure_interior (X := X) (A := A)
    have hsubset' : interior (A : Set X) ⊆ (∅ : Set X) := by
      simpa [h] using hsubset
    -- Conclude the desired equality.
    apply Set.Subset.antisymm hsubset'
    intro x hx; cases hx
  · intro h
    -- Rewrite using `h` to reduce to the empty set.
    simpa [h, closure_empty, interior_empty]

theorem Topology.interior_closure_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure (A : Set X))) = interior (closure A) := by
  simpa [closure_closure]

theorem Topology.interior_closure_inter_closure_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((closure A) ∩ (closure B) : Set X) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hxA : x ∈ interior (closure A) := by
    -- `closure A ∩ closure B ⊆ closure A`
    have h₁ : (closure A ∩ closure B : Set X) ⊆ closure A :=
      Set.inter_subset_left
    -- Monotonicity of `interior`
    have h₂ :
        interior (closure A ∩ closure B : Set X) ⊆ interior (closure A) :=
      interior_mono h₁
    exact h₂ hx
  -- Membership in `interior (closure B)`
  have hxB : x ∈ interior (closure B) := by
    -- `closure A ∩ closure B ⊆ closure B`
    have h₁ : (closure A ∩ closure B : Set X) ⊆ closure B :=
      Set.inter_subset_right
    -- Monotonicity of `interior`
    have h₂ :
        interior (closure A ∩ closure B : Set X) ⊆ interior (closure B) :=
      interior_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB

theorem Topology.closure_eq_univ_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro h_cl
    -- Rewrite the left-hand side in the desired equality.
    simpa [h_cl, interior_univ]
  · intro h_int
    -- From `interior (closure A) = univ` we get `univ ⊆ closure A`.
    have h_sub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      have : interior (closure (A : Set X)) ⊆ closure A := interior_subset
      simpa [h_int] using this
    -- The reverse inclusion is trivial.
    have h_sup : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x _; simp
    exact Set.Subset.antisymm h_sup h_sub

theorem Topology.P2_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B)
    (hB : B ⊆ interior (closure (interior A))) :
    Topology.P2 (X := X) B := by
  dsimp [Topology.P2] at *
  intro x hxB
  -- From the hypothesis `hB`, `x` lies in `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hB hxB
  -- We show that this set is contained in `interior (closure (interior B))`.
  have h_incl :
      interior (closure (interior A)) ⊆
        interior (closure (interior B)) := by
    -- Step 1: `interior A ⊆ interior B` since `A ⊆ B`.
    have h₁ : (interior A : Set X) ⊆ interior B :=
      interior_mono hAB
    -- Step 2: take closures.
    have h₂ : closure (interior A : Set X) ⊆ closure (interior B) :=
      closure_mono h₁
    -- Step 3: take interiors once more.
    exact interior_mono h₂
  -- Conclude that `x ∈ interior (closure (interior B))`.
  exact h_incl hx₁

theorem Topology.interior_closure_union_eq_interior_union_closures
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (closure (A ∪ B : Set X)) =
      interior (closure A ∪ closure B) := by
  simp [closure_union]

theorem Topology.closure_interior_eq_univ_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (Set.univ : Set X) ↔
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
  simpa using
    (Topology.closure_eq_univ_iff_interior_closure_eq_univ
      (X := X) (A := interior A))

theorem Topology.P3_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (X := X) (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  simpa using
    Topology.isOpen_P3 (X := X)
      (A := interior (closure (interior (closure A)))) h_open

theorem interior_union {α : Type*} [TopologicalSpace α] {A B : Set α} :
    (interior (A : Set α)) ∪ interior B ⊆ interior (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- `interior A ⊆ interior (A ∪ B)` because `A ⊆ A ∪ B`.
      have h_sub : (interior (A : Set α)) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_left : (A : Set α) ⊆ A ∪ B)
      exact h_sub hA
  | inr hB =>
      -- Symmetric argument for `interior B`.
      have h_sub : (interior (B : Set α)) ⊆ interior (A ∪ B) :=
        interior_mono (Set.subset_union_right : (B : Set α) ⊆ A ∪ B)
      exact h_sub hB



theorem Topology.interior_closure_iter_three_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := closure (A : Set X)))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq
              (X := X) (A := A))

theorem Topology.P2_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P2 (X := X) (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  simpa using
    Topology.isOpen_P2 (X := X)
      (A := interior (closure (interior (closure A)))) h_open

theorem Topology.P1_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem Topology.subset_interior_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure (A : Set X))) :
    (A : Set X) ⊆ interior (closure A) := by
  intro x hxA
  have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  simpa [h.interior_eq] using hx_closure

theorem Topology.P2_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x _
  simp [interior_univ, closure_univ]

theorem Topology.P3_of_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hB : B ⊆ interior (closure A)) :
    Topology.P3 (X := X) B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- Use the assumption `hB` to place `x` inside `interior (closure A)`.
  have hx_intA : x ∈ interior (closure A) := hB hxB
  -- Monotonicity: `closure A ⊆ closure B` because `A ⊆ B`.
  have h_closure_mono : closure A ⊆ closure B := closure_mono hAB
  -- Hence, `interior (closure A) ⊆ interior (closure B)`.
  have h_int_mono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure_mono
  -- Conclude that `x ∈ interior (closure B)`.
  exact h_int_mono hx_intA

theorem Topology.P3_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : IsOpen (closure (A : Set X))) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  exact Topology.subset_interior_closure_of_isOpen_closure (X := X) (A := A) h

theorem Topology.interior_iInter_closure_subset_iInter_interior_closure
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (⋂ i, closure (A i) : Set X) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each index `i`, we show `x ∈ interior (closure (A i))`.
  have h_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- `⋂ i, closure (A i) ⊆ closure (A i)`.
    have h_subset :
        (⋂ j, closure (A j) : Set X) ⊆ closure (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `interior`.
    have h_int :
        interior (⋂ j, closure (A j) : Set X) ⊆ interior (closure (A i)) :=
      interior_mono h_subset
    exact h_int hx
  -- Combine the pointwise statements into one for the intersection.
  exact (Set.mem_iInter.2 h_i)

theorem Topology.interior_iInter_subset_iInter_interior
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (⋂ i, A i : Set X) ⊆ ⋂ i, interior (A i) := by
  intro x hx
  -- Show that `x` belongs to each `interior (A i)`.
  have hx_each : ∀ i, x ∈ interior (A i) := by
    intro i
    -- Since `⋂ i, A i ⊆ A i`, monotonicity of `interior` yields the result.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_int : interior (⋂ j, A j : Set X) ⊆ interior (A i) :=
      interior_mono h_subset
    exact h_int hx
  -- Combine the pointwise facts into a membership of the intersection.
  exact (Set.mem_iInter.2 hx_each)

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure B)) := by
  -- Step 1: Enlarge `closure A` to `closure B` using monotonicity of `closure`.
  have h₁ : (closure (A : Set X)) ⊆ closure B := closure_mono hAB
  -- Step 2: Apply monotonicity of `interior` to the previous inclusion.
  have h₂ : (interior (closure (A : Set X)) : Set X) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Step 3: Take closures of both sides to obtain the desired inclusion.
  exact closure_mono h₂

theorem Topology.P2_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    Topology.P1 (X := X) A := by
  -- First upgrade `P2` to `P3`.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Then invoke the closed‐set lemma turning `P3` into `P1`.
  exact
    Topology.P3_implies_P1_of_isClosed
      (X := X) (A := A) h_closed hP3

theorem Topology.P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X := X) (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x _
  simp [closure_univ, interior_univ]

theorem Topology.closure_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    closure (A : Set X) = closure (interior (closure A)) := by
  -- `P1` for `A` yields `P1` for `closure A`.
  have hP1_closure : Topology.P1 (X := X) (closure A) :=
    Topology.P1_closure_of_P1 (X := X) (A := A) hA
  -- Apply the equality given by `P1` to `closure A`.
  have h_eq :
      closure (closure (A : Set X)) = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_of_P1
      (X := X) (A := closure A) hP1_closure
  -- Simplify `closure (closure A)` to `closure A`.
  simpa [closure_closure] using h_eq

theorem Topology.interior_closure_interior_closure_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆
      interior (closure A) := by
  simpa [closure_closure] using
    (Topology.interior_closure_interior_subset_interior_closure
      (X := X) (A := closure A))

theorem Topology.iUnion_interior_subset_interior_iUnion {X ι : Type*}
    [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (A i) : Set X) ⊆ interior (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Use monotonicity of `interior` with the inclusion `A i ⊆ ⋃ j, A j`.
  have h_sub : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
    have : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono this
  exact h_sub hxAi

theorem Topology.closure_iUnion_interior_subset_closure_interior_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, closure (interior (A i)) : Set X) ⊆
      closure (interior (⋃ i, A i)) := by
  intro x hx
  -- Choose an index `i` such that `x ∈ closure (interior (A i))`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- The inclusion `A i ⊆ ⋃ j, A j` lifts to interiors via monotonicity.
  have h_int :
      (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
    have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact interior_mono h_subset
  -- Taking closures preserves this inclusion.
  have h_closure :
      closure (interior (A i) : Set X) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int
  -- Conclude that `x ∈ closure (interior (⋃ j, A j))`.
  exact h_closure hx_i

theorem Topology.interior_closure_eq_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior A := by
  simpa [hA.closure_eq]

theorem Topology.P1_of_isClosed_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x hx
  -- Since `A` is open, its interior is itself.
  have h_int : interior (A : Set X) = A := by
    simpa using h_open.interior_eq
  -- Consequently, because `A` is closed, the closure of its interior is also `A`.
  have h_closure : closure (interior (A : Set X)) = A := by
    have : closure (interior (A : Set X)) = closure (A : Set X) := by
      simpa [h_int]
    simpa [h_closed.closure_eq] using this
  -- The desired membership follows by rewriting with `h_closure`.
  simpa [h_closure] using hx

theorem Topology.interior_closure_interior_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior A))) =
      interior (closure (interior A)) := by
  simpa [interior_interior]

theorem Topology.interior_closure_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simpa [closure_empty, interior_empty]

theorem Topology.P3_of_interior_closure_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 (X := X) A := by
  dsimp [Topology.P3]
  intro x hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using hx_univ

theorem Topology.isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    IsOpen (A : Set X) := by
  exact
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP2

theorem Topology.closure_interior_eq_self_of_isClosed_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- Since `A` is open, its interior is itself.
  have h_int : interior (A : Set X) = A := h_open.interior_eq
  -- Since `A` is closed, its closure is itself.
  have h_closure : closure (A : Set X) = A := h_closed.closure_eq
  -- Rewrite and finish.
  calc
    closure (interior (A : Set X)) = closure (A : Set X) := by
      simpa [h_int]
    _ = A := h_closure

theorem Topology.interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]

theorem Topology.interior_closure_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆
      interior (closure (interior (closure A))) := by
  -- `interior (closure A)` is open.
  have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  -- And it is contained in `closure (interior (closure A))`.
  have h_subset :
      (interior (closure (A : Set X)) : Set X) ⊆
        closure (interior (closure (A : Set X))) :=
    subset_closure
  -- Apply the maximality property of the interior for an open set.
  exact interior_maximal h_subset h_open

theorem Topology.closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure A)) := by
  simpa [closure_closure]

theorem Topology.P1_P2_P3_of_isClosed_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  -- `P1` follows from the combination of closedness and openness of `A`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_isClosed_isOpen (X := X) (A := A) h_closed h_open
  -- `P2` holds for any open set.
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_P2 (X := X) (A := A) h_open
  -- `P3` is equivalent to openness for closed sets, hence holds as well.
  have hP3 : Topology.P3 (X := X) A := by
    have h_equiv := Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed
    exact (h_equiv.mpr h_open)
  exact And.intro hP1 (And.intro hP2 hP3)

theorem Topology.P3_union_three_of_P2 {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hA : Topology.P2 (X := X) A)
    (hB : Topology.P2 (X := X) B) (hC : Topology.P2 (X := X) C) :
    Topology.P3 (X := X) (A ∪ B ∪ C) := by
  -- Upgrade each `P2` hypothesis to `P3`.
  have hA3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  have hB3 : Topology.P3 (X := X) B :=
    Topology.P2_implies_P3 (X := X) (A := B) hB
  have hC3 : Topology.P3 (X := X) C :=
    Topology.P2_implies_P3 (X := X) (A := C) hC
  -- First union `A` and `B`.
  have hAB3 : Topology.P3 (X := X) (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA3 hB3
  -- Then union the result with `C`.
  have hABC3 : Topology.P3 (X := X) ((A ∪ B) ∪ C) :=
    Topology.P3_union (X := X) (A := (A ∪ B)) (B := C) hAB3 hC3
  -- Rewrite with associativity of union.
  simpa [Set.union_assoc] using hABC3

theorem Topology.P1_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P1 (X := X) (interior (closure (interior (closure A)))) := by
  have h_open : IsOpen (interior (closure (interior (closure A)))) := isOpen_interior
  simpa using
    Topology.isOpen_P1 (X := X)
      (A := interior (closure (interior (closure A)))) h_open

theorem Topology.isOpen_closure_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (closure (A : Set X))) :
    IsOpen (closure A) := by
  exact
    (Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)).1 h

theorem Topology.P1_P2_P3_of_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = A) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  -- From the equality `interior A = A`, we deduce that `A` is open.
  have h_open : IsOpen (A : Set X) := by
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [h] using this
  -- Apply the existing triple property for open sets.
  exact Topology.P1_P2_P3_of_isOpen (X := X) (A := A) h_open

theorem Topology.interior_inter_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) = interior A ∩ interior B := by
  -- First, establish the inclusion `⊆`.
  have h₁ :
      interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact And.intro hxA hxB
  -- Next, establish the inclusion `⊇`.
  have h₂ :
      interior A ∩ interior B ⊆ interior (A ∩ B : Set X) := by
    -- The set `interior A ∩ interior B` is open …
    have h_open : IsOpen (interior A ∩ interior B : Set X) :=
      (isOpen_interior : IsOpen (interior A)).inter
        (isOpen_interior : IsOpen (interior B))
    -- … and contained in `A ∩ B`.
    have h_sub :
        (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro x hx
      exact And.intro
        ((interior_subset : interior A ⊆ A) hx.1)
        ((interior_subset : interior B ⊆ B) hx.2)
    -- Hence it is contained in the interior of `A ∩ B`.
    exact interior_maximal h_sub h_open
  -- Combine the two inclusions into an equality.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.closure_interior_iter_five_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))))) =
        closure (interior (closure (interior A))) := by
          simpa [Topology.closure_interior_iter_four_eq (X := X) (A := A)]
    _ = closure (interior A) := by
          simpa using
            Topology.closure_interior_closure_interior_eq (X := X) (A := A)

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure A := by
  exact Set.Subset.trans interior_subset subset_closure

theorem Topology.closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ, closure_univ]

theorem Topology.interior_eq_empty_of_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (closure (A : Set X)) = (∅ : Set X)) :
    interior (A : Set X) = (∅ : Set X) := by
  -- `interior A` is always contained in `interior (closure A)`.
  have hsubset : (interior (A : Set X)) ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Hence, by the hypothesis, `interior A` is contained in `∅`.
  have hsubset' : (interior (A : Set X)) ⊆ (∅ : Set X) := by
    simpa [h] using hsubset
  -- Conclude the desired equality by antisymmetry.
  apply Set.Subset.antisymm hsubset'
  intro x hx; cases hx

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- `closure (interior A)` is always contained in `closure A`.
  have h_subset : (closure (interior (A : Set X))) ⊆ closure A :=
    closure_mono (interior_subset : (interior (A : Set X)) ⊆ A)
  -- Hence, from the hypothesis, `univ ⊆ closure A`.
  have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
    simpa [hA] using h_subset
  -- The reverse inclusion is immediate.
  have h_closure_subset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro x _; simp
  -- Conclude the desired equality.
  exact Set.Subset.antisymm h_closure_subset h_univ_subset

theorem Topology.closure_iInter_subset_iInter_closure
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋂ i, A i : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each index `i`, we show that `x ∈ closure (A i)`.
  have h_i : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The intersection is contained in each `A i`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` gives the desired inclusion.
    have h_closure :
        closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure hx
  -- Combine the pointwise facts into the desired membership.
  exact (Set.mem_iInter.2 h_i)

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  -- We show the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    -- From `P2` we already have the key inclusion on interiors.
    have h₁ :
        (interior (closure (A : Set X)) : Set X) ⊆ closure (interior A) :=
      Topology.interior_closure_subset_closure_interior_of_P2
        (X := X) (A := A) hA
    -- Taking closures preserves inclusion; simplify the right‐hand side.
    have h₂ :
        closure (interior (closure (A : Set X))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `⊇` direction
    -- `interior A` is contained in `interior (closure A)`.
    have h₁ :
        (interior (A : Set X)) ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (X := X) (A := A)
    -- Taking closures yields the desired inclusion.
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure A)) :=
      closure_mono h₁
    simpa using h₂

theorem Topology.closure_interior_inter_eq_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) = closure (interior A ∩ interior B) := by
  simpa [Topology.interior_inter_eq (X := X) (A := A) (B := B)]

theorem Topology.closure_interior_closure_eq_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  -- From `P1` we know that the closures of `A` and `interior A` coincide.
  have h_cl : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  -- Rewrite the left‐hand side using `h_cl` and invoke the idempotence lemma.
  calc
    closure (interior (closure (A : Set X))) =
        closure (interior (closure (interior A))) := by
          simpa [h_cl]
    _ = closure (interior A) := by
          simpa using
            Topology.closure_interior_closure_interior_eq (X := X) (A := A)

theorem Topology.interior_diff_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  simpa using
    interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)

theorem Topology.closure_inter_subset_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A := by
    have h_sub : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono h_sub) hx
  have hxB : x ∈ closure B := by
    have h_sub : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (closure_mono h_sub) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_union_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ∪ closure (interior A) ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hx_int =>
      -- `x ∈ interior (closure A)` and this set is contained in `closure A`.
      have h_sub : interior (closure (A : Set X)) ⊆ closure A :=
        interior_subset
      exact h_sub hx_int
  | inr hx_cl =>
      -- `x ∈ closure (interior A)` and this set is contained in `closure A`.
      have h_sub : closure (interior (A : Set X)) ⊆ closure A :=
        Topology.closure_interior_subset_closure (X := X) (A := A)
      exact h_sub hx_cl

theorem Topology.P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) := by
  -- Existing equivalences for open sets.
  have h₁ : Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP2
    -- Obtain `P1` from `P2`, then `P3` from `P1`.
    have hP1 : Topology.P1 (X := X) A := h₁.mpr hP2
    have hP3 : Topology.P3 (X := X) A := h₂.mp hP1
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- Convert `P1` back to `P2`.
    exact h₁.mp hP1

theorem Topology.closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closure_interior_closure_interior_eq
      (X := X) (A := closure A))

theorem Topology.isClosed_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X))) := by
  simpa using isClosed_closure

theorem Topology.interior_closure_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X)) ⊆ interior (closure (A ∪ B : Set X)) := by
  exact
    Topology.interior_closure_mono
      (X := X) (A := A) (B := A ∪ B)
      (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)

theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) (closure A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.isOpen_P1 (X := X) (A := A) hA
  exact Topology.P1_closure_of_P1 (X := X) (A := A) hP1

theorem Topology.interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (A : Set X) ⊆ interior (closure B) := by
  intro x hxA
  -- Step 1: `x` belongs to `interior B` because `A ⊆ B`.
  have hxB : x ∈ interior B := (interior_mono hAB) hxA
  -- Step 2: `interior B` is contained in `interior (closure B)`.
  have h_sub : (interior B : Set X) ⊆ interior (closure B) :=
    interior_mono (subset_closure : (B : Set X) ⊆ closure B)
  exact h_sub hxB

theorem Topology.interior_iUnion_eq_iUnion_of_isOpen
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, IsOpen (A i)) :
    interior (⋃ i, A i : Set X) = ⋃ i, A i := by
  -- The union of open sets is open.
  have h_open : IsOpen (⋃ i, A i : Set X) := isOpen_iUnion (fun i ↦ hA i)
  -- For an open set `U`, `interior U = U`.
  simpa [h_open.interior_eq]

theorem Topology.P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  have h_equiv := Topology.P2_iff_P3_of_isClosed (X := X) (A := A) h_closed
  exact h_equiv.mpr hP3

theorem Topology.interior_closure_eq_interior_closure_interior_of_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = closure (interior A)) :
    interior (closure (A : Set X)) =
      interior (closure (interior A)) := by
  simpa [h]

theorem Topology.P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (∅ : Set X) := by
  dsimp [Topology.P2]
  simp

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, which is `∅` by hypothesis.
    have h_subset : (interior (A : Set X)) ⊆ (∅ : Set X) := by
      have : (interior (A : Set X)) ⊆ closure (interior (A : Set X)) :=
        subset_closure
      simpa [h] using this
    -- Hence, `interior A = ∅`.
    exact Set.Subset.antisymm h_subset (Set.empty_subset _)
  · intro h
    -- Rewrite with `h` and simplify using `closure_empty`.
    simpa [h] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))

theorem Topology.closure_interior_eq_univ_of_P1_and_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A)
    (h_dense : closure (A : Set X) = (Set.univ : Set X)) :
    closure (interior A) = (Set.univ : Set X) := by
  -- From `P1` we know the two closures coincide.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  -- Rewrite `h_dense` via `h_eq` to obtain the desired equality.
  calc
    closure (interior A) = closure (A : Set X) := by
      simpa using h_eq.symm
    _ = (Set.univ : Set X) := h_dense

theorem Topology.interior_union_eq_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = A ∪ B := by
  have h_open : IsOpen (A ∪ B : Set X) := hA.union hB
  simpa [h_open.interior_eq]

theorem Topology.P2_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior A) ↔ Topology.P3 (X := X) (interior A) := by
  -- `interior A` is an open set.
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Apply the general equivalence for open sets.
  simpa using
    (Topology.P2_iff_P3_of_isOpen (X := X) (A := interior A) h_open)

theorem Topology.P1_P2_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) :
    (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) ↔
      IsOpen (A : Set X) := by
  constructor
  · intro h
    -- Extract `P2 A` from the triple.
    have hP2 : Topology.P2 (X := X) A := h.2.1
    -- Convert `P2 A` to openness using the closed‐set equivalence.
    exact
      (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP2
  · intro h_open
    -- For an open set, all three properties hold.
    exact Topology.P1_P2_P3_of_isOpen (X := X) (A := A) h_open

theorem Topology.interior_closure_union_three_subset {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior (closure (A : Set X)) ∪ interior (closure B) ∪ interior (closure C) ⊆
      interior (closure (A ∪ B ∪ C : Set X)) := by
  -- First, deal with the union of `A` and `B`.
  have hAB :
      interior (closure (A : Set X)) ∪ interior (closure B) ⊆
        interior (closure (A ∪ B : Set X)) :=
    Topology.interior_closure_union_subset (X := X) (A := A) (B := B)
  -- Next, add `C` to the picture.
  have hABC :
      interior (closure (A ∪ B : Set X)) ∪ interior (closure C) ⊆
        interior (closure ((A ∪ B) ∪ C : Set X)) :=
    Topology.interior_closure_union_subset (X := X) (A := A ∪ B) (B := C)
  -- Rewrite `((A ∪ B) ∪ C)` using associativity.
  have hABC' :
      interior (closure (A ∪ B : Set X)) ∪ interior (closure C) ⊆
        interior (closure (A ∪ B ∪ C : Set X)) := by
    simpa [Set.union_assoc] using hABC
  -- Now prove the desired inclusion.
  intro x hx
  -- Analyse the membership of `x` in the triple union.
  cases hx with
  | inl hx_left =>
      -- `x` lies in the first two terms of the triple union.
      have hxAB : x ∈ interior (closure (A ∪ B : Set X)) := hAB hx_left
      have hxABC : x ∈
          interior (closure (A ∪ B : Set X)) ∪ interior (closure C) :=
        Or.inl hxAB
      exact hABC' hxABC
  | inr hxC =>
      -- `x` lies in the third term `interior (closure C)`.
      have hxABC : x ∈
          interior (closure (A ∪ B : Set X)) ∪ interior (closure C) :=
        Or.inr hxC
      exact hABC' hxABC

theorem Topology.P2_closure_interior_iff_P3_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (closure (interior A)) ↔
      Topology.P3 (X := X) (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P2_iff_P3_of_isClosed
      (X := X) (A := closure (interior A)) h_closed)

theorem Topology.closure_interior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ∪ closure (interior C) ⊆
      closure (interior (A ∪ B ∪ C : Set X)) := by
  -- Each individual term of the left‐hand side is contained in the right‐hand side.
  have hA :
      closure (interior (A : Set X)) ⊆
        closure (interior (A ∪ B ∪ C : Set X)) := by
    apply Topology.closure_interior_mono
    intro x hx
    -- `x ∈ A ⊆ A ∪ B ∪ C`
    exact Or.inl (Or.inl hx)
  have hB :
      closure (interior (B : Set X)) ⊆
        closure (interior (A ∪ B ∪ C : Set X)) := by
    apply Topology.closure_interior_mono
    intro x hx
    -- `x ∈ B ⊆ A ∪ B ⊆ (A ∪ B) ∪ C`
    exact Or.inl (Or.inr hx)
  have hC :
      closure (interior (C : Set X)) ⊆
        closure (interior (A ∪ B ∪ C : Set X)) := by
    apply Topology.closure_interior_mono
    intro x hx
    -- `x ∈ C ⊆ (A ∪ B) ∪ C`
    exact Or.inr hx
  -- Analyse membership in the triple union.
  intro x hx
  cases hx with
  | inl hxAB =>
      cases hxAB with
      | inl hxA => exact hA hxA
      | inr hxB => exact hB hxB
  | inr hxC => exact hC hxC

theorem Topology.interior_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ⊆ closure (interior A) := by
  exact subset_closure

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (closure A)) := by
  -- Step 1: enlarge `interior A` to `interior (closure A)` using monotonicity
  -- of `interior` with respect to the inclusion `A ⊆ closure A`.
  have h₁ :
      (interior (A : Set X)) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Step 2: every set is contained in the closure of itself.
  have h₂ :
      (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
    subset_closure
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Topology.interior_closure_interior_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (closure (interior A)) = interior A := by
  -- First inclusion: `⊆`
  have h₁ : closure (interior A : Set X) ⊆ A := by
    have h_cl : closure (interior A : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [hA.closure_eq] using h_cl
  have h_left : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h₁
  -- Second inclusion: `⊇`
  have h₂ : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  have h_right : interior A ⊆ interior (closure (interior A)) :=
    interior_maximal h₂ h_open
  -- Combine the inclusions to obtain the desired equality.
  exact Set.Subset.antisymm h_left h_right

theorem Topology.closure_iInter_interior_subset_iInter_closure_interior
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋂ i, interior (A i) : Set X) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- Show that `x` belongs to each `closure (interior (A i))`.
  have hx_i : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `⋂ i, interior (A i) ⊆ interior (A i)`.
    have h_subset : (⋂ j, interior (A j) : Set X) ⊆ interior (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Apply monotonicity of `closure`.
    have h_closure :
        closure (⋂ j, interior (A j) : Set X) ⊆ closure (interior (A i)) :=
      closure_mono h_subset
    exact h_closure hx
  -- Combine the pointwise memberships into the intersection.
  exact (Set.mem_iInter.2 hx_i)

theorem Topology.interior_closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B : Set X)) ⊆
      interior (closure (A ∩ B : Set X)) := by
  -- First, observe the basic inclusion `A ∩ interior B ⊆ A ∩ B`.
  have h_subset : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    have hB : (interior B : Set X) ⊆ B := interior_subset
    exact Set.inter_subset_inter_right _ hB
  -- Apply monotonicity of `closure`.
  have h_closure :
      closure (A ∩ interior B : Set X) ⊆ closure (A ∩ B) :=
    closure_mono h_subset
  -- Apply monotonicity of `interior` to obtain the desired inclusion.
  exact interior_mono h_closure



theorem Topology.closure_interior_diff_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- `A \ B` is a subset of `A`.
  have h_subset : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Apply monotonicity of `interior` to the subset inclusion.
  have h_int : (interior (A \ B : Set X) : Set X) ⊆ interior A :=
    interior_mono h_subset
  -- Take closures to obtain the desired inclusion.
  exact closure_mono h_int

theorem Topology.closure_inter_interior_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Show `x ∈ closure A`.
  have hxA : x ∈ closure A := by
    -- `A ∩ interior B ⊆ A`.
    have h_sub : (A ∩ interior B : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono h_sub) hx
  -- Show `x ∈ closure B`.
  have hxB : x ∈ closure B := by
    -- `interior B ⊆ B`.
    have h_int_subset : (interior B : Set X) ⊆ B := interior_subset
    -- Hence `A ∩ interior B ⊆ B`.
    have h_sub : (A ∩ interior B : Set X) ⊆ B := by
      intro y hy
      exact h_int_subset hy.2
    exact (closure_mono h_sub) hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    interior (closure (A : Set X)) = closure A := by
  -- `closure A` is always closed.
  have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
  -- Apply the existing lemma for sets that are both closed and open.
  simpa [closure_closure] using
    Topology.interior_closure_eq_self_of_isClosed_isOpen
      (X := X) (A := closure A) h_closed h_open

theorem Topology.P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (X := X) (∅ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  cases hx

theorem Topology.interior_diff_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior (closure A) := by
  -- First include `A \ B ⊆ A`, then apply monotonicity of `interior`.
  have h₁ : interior (A \ B : Set X) ⊆ interior A :=
    interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)
  -- Next, use the general inclusion `interior A ⊆ interior (closure A)`.
  have h₂ : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂

theorem Topology.P2_iff_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (Set.univ : Set X) ↔
      Topology.P3 (X := X) (Set.univ : Set X) := by
  constructor
  · intro _
    exact Topology.P3_univ (X := X)
  · intro _
    exact Topology.P2_univ (X := X)

theorem Topology.interior_closure_interior_closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
      interior (closure (interior A)) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
        interior (closure (interior (closure (interior (A : Set X))))) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := closure (interior (A : Set X))))
    _ = interior (closure (interior A)) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := A))

theorem Topology.closure_interior_union_eq_closure_union_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) =
      closure (interior A ∪ interior B) := by
  simpa using
    (closure_union (interior (A : Set X)) (interior (B : Set X))).symm

theorem Topology.P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A) := by
  -- Established equivalences for open sets.
  have h₁ : Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP3
    -- Derive `P1` and `P2` from `P3`.
    have hP1 : Topology.P1 (X := X) A := h₁.mpr hP3
    have hP2 : Topology.P2 (X := X) A := h₂.mpr hP3
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _⟩
    -- Recover `P3` from `P1`.
    exact h₁.mp hP1

theorem Topology.interior_subset_closure_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ⊆ closure (interior (A ∪ B)) := by
  intro x hx
  -- Step 1: enlarge `interior A` to `interior (A ∪ B)` using monotonicity of `interior`.
  have hx_union : x ∈ interior (A ∪ B) :=
    (interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)) hx
  -- Step 2: every set is contained in the closure of itself.
  have h_closure :
      (interior (A ∪ B) : Set X) ⊆ closure (interior (A ∪ B)) :=
    subset_closure
  -- Step 3: assemble the two inclusions.
  exact h_closure hx_union

theorem Topology.P3_union_of_P2_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- Upgrade the `P2` hypothesis on `A` to `P3`.
  have hA3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  -- Combine the `P3` properties using the union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := B) hA3 hB

theorem Topology.P2_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P2 (X := X) A) :
    Topology.P2 (X := X) (A ∪ interior B) := by
  -- `P2` holds for `interior B` because it is an open set.
  have hB : Topology.P2 (X := X) (interior B) :=
    Topology.P2_interior (X := X) (A := B)
  -- Use the existing union lemma for `P2`.
  simpa using
    Topology.P2_union (X := X) (A := A) (B := interior B) hA hB

theorem Topology.iUnion_interior_closure_subset_interior_closure_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, interior (closure (A i)) : Set X) ⊆
      interior (closure (⋃ i, A i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have h_sub :
      (interior (closure (A i)) : Set X) ⊆
        interior (closure (⋃ j, A j : Set X)) := by
    -- First, relate the closures of the sets.
    have h_closure :
        (closure (A i : Set X)) ⊆ closure (⋃ j, A j) := by
      have : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono this
    -- Then, pass to interiors via monotonicity.
    exact interior_mono h_closure
  exact h_sub hx_i

theorem Topology.closure_union_interiors_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∪ interior B) ⊆
      closure (interior (A ∪ B : Set X)) := by
  -- The union of the interiors is contained in the interior of the union.
  have h_subset :
      (interior (A : Set X) ∪ interior B : Set X) ⊆ interior (A ∪ B) :=
    Topology.interior_union_subset (X := X) (A := A) (B := B)
  -- Taking closures preserves the inclusion.
  exact closure_mono h_subset

theorem Topology.P2_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    Topology.P2 (X := X) (closure A) := by
  have h_equiv := Topology.P2_closure_iff_isOpen_closure (X := X) (A := A)
  exact h_equiv.mpr h_open

theorem Topology.closure_diff_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A := by
  -- The set difference `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Monotonicity of `closure` yields the desired inclusion.
  exact closure_mono h_subset

theorem Topology.iUnion_closure_subset_closure_iUnion {X ι : Type*}
    [TopologicalSpace X] (A : ι → Set X) :
    (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `A i ⊆ ⋃ j, A j`
  have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  -- Taking closures preserves the inclusion.
  have h_closure : closure (A i : Set X) ⊆ closure (⋃ j, A j) :=
    closure_mono h_subset
  exact h_closure hx_i

theorem Topology.P1_union_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P1 (X := X) (interior A ∪ interior B) := by
  -- `P1` holds for the interior of any set.
  have hA : Topology.P1 (X := X) (interior A) :=
    Topology.P1_interior (X := X) (A := A)
  have hB : Topology.P1 (X := X) (interior B) :=
    Topology.P1_interior (X := X) (A := B)
  -- Combine the two `P1` properties using the union lemma.
  simpa using
    Topology.P1_union (X := X) (A := interior A) (B := interior B) hA hB

theorem Topology.P2_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior A)) ↔
      IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is a closed set.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Apply the closed‐set characterization of `P2`.
  simpa using
    (Topology.P2_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior A)) h_closed)

theorem Topology.interior_diff_closed_eq {X : Type*} [TopologicalSpace X]
    {A C : Set X} (hC : IsClosed (C : Set X)) :
    interior (A \ C : Set X) = interior A \ C := by
  -- First, prove the inclusion `⊆`.
  have h₁ : interior (A \ C : Set X) ⊆ interior A \ C := by
    intro x hx
    -- From `x ∈ interior (A \ C)` we get `x ∈ interior A`.
    have hxA : x ∈ interior A :=
      (interior_mono (Set.diff_subset : (A \ C : Set X) ⊆ A)) hx
    -- And `x ∉ C`, since `x` actually lies in `A \ C`.
    have hxNC : x ∉ C := by
      have : x ∈ (A \ C : Set X) := interior_subset hx
      exact this.2
    exact And.intro hxA hxNC
  -- Next, prove the inclusion `⊇`.
  have h₂ : interior A \ C ⊆ interior (A \ C : Set X) := by
    intro x hx
    rcases hx with ⟨hxA, hxNC⟩
    -- Construct an open neighbourhood of `x` contained in `A \ C`.
    have h_open_int : IsOpen (interior (A : Set X)) := isOpen_interior
    have h_open_compl : IsOpen (Cᶜ : Set X) := hC.isOpen_compl
    have h_open : IsOpen (interior A ∩ Cᶜ : Set X) :=
      h_open_int.inter h_open_compl
    have hx_in : x ∈ (interior A ∩ Cᶜ : Set X) := And.intro hxA hxNC
    -- Show this neighbourhood is contained in `A \ C`.
    have h_subset :
        (interior A ∩ Cᶜ : Set X) ⊆ (A \ C : Set X) := by
      intro y hy
      have hyA : y ∈ A := (interior_subset : interior A ⊆ A) hy.1
      exact And.intro hyA hy.2
    -- Apply maximality of the interior.
    have h_interior :
        (interior A ∩ Cᶜ : Set X) ⊆ interior (A \ C : Set X) :=
      interior_maximal h_subset h_open
    exact h_interior hx_in
  -- Combine the two inclusions.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.P3_closure_interior_iff_isOpen_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  -- `closure (interior A)` is a closed set, so we may apply the general equivalence.
  have h_closed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_iff_isOpen_of_isClosed
      (X := X) (A := closure (interior A)) h_closed)

theorem Topology.closure_subset_closure_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ interior (closure B)) :
    closure (A : Set X) ⊆ closure B := by
  -- First, enlarge `A` to `interior (closure B)` using `h`, then take closures.
  have h₁ : closure (A : Set X) ⊆ closure (interior (closure B)) :=
    closure_mono h
  -- Next, observe that `interior (closure B)` is contained in `closure B`,
  -- hence so is its closure.
  have h₂ : closure (interior (closure B)) ⊆ closure B := by
    have h_sub : (interior (closure B) : Set X) ⊆ closure B := interior_subset
    simpa [closure_closure] using closure_mono h_sub
  -- Combine the two inclusions to obtain the desired result.
  exact Set.Subset.trans h₁ h₂

theorem Topology.P3_union_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P3 (X := X) A) :
    Topology.P3 (X := X) (A ∪ interior B) := by
  -- `P3` holds for `interior B` because it is an open set.
  have hB : Topology.P3 (X := X) (interior B) :=
    Topology.P3_interior (X := X) (A := B)
  -- Combine the two `P3` properties via the existing union lemma.
  exact Topology.P3_union (X := X) (A := A) (B := interior B) hA hB

theorem Topology.interior_closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    interior (closure (A : Set X)) ⊆ closure (interior A) := by
  -- From `P1` we have `closure A = closure (interior A)`.
  have h_eq : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  -- Now show the required inclusion.
  intro x hx
  -- `x` lies in `closure A` because interiors are contained in the set itself.
  have hx_cl : x ∈ closure (A : Set X) :=
    (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hx
  -- Rewrite with the equality of closures obtained from `P1`.
  simpa [h_eq] using hx_cl

theorem Topology.open_subset_closure_implies_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen (U : Set X)) (h_subset : (U : Set X) ⊆ closure (A : Set X)) :
    (U : Set X) ⊆ interior (closure A) := by
  exact interior_maximal h_subset hU

theorem Topology.closure_interior_diff_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior (closure A)) := by
  exact
    Set.Subset.trans
      (Topology.closure_interior_diff_subset_closure_interior
        (X := X) (A := A) (B := B))
      (Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A))

theorem Topology.P3_implies_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  have h_equiv := Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  exact h_equiv.mpr hP3

theorem Topology.P2_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure A)) :
    Topology.P2 (X := X) (closure A) := by
  -- Use the equivalence between `P2` and `P3` for closed sets.
  exact
    ((Topology.P2_closure_iff_P3_closure (X := X) (A := A)).symm).mp h

theorem Topology.closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- First, `closure (interior A)` is contained in `closure A` by monotonicity.
  have h_sub : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : (interior (A : Set X)) ⊆ A)
  -- Since `A` is closed, `closure A = A`; rewrite and finish.
  simpa [hA.closure_eq] using h_sub

theorem Topology.P2_union_interior_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (interior A ∪ B) := by
  -- Reuse the “right‐hand side” lemma with the arguments swapped.
  have h := Topology.P2_union_interior_right (X := X) (A := B) (B := A) hB
  simpa [Set.union_comm] using h

theorem Topology.P2_closure_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 (X := X) (closure A) := by
  -- First, show that `closure (interior (closure A)) = univ`.
  have h_dense : closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure (interior (closure A))`.
    have h_subset :
        closure (interior (A : Set X)) ⊆
          closure (interior (closure A)) :=
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A)
    -- Hence `univ ⊆ closure (interior (closure A))`.
    have h_univ_subset :
        (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
      simpa [h] using h_subset
    -- The reverse inclusion is trivial.
    have h_subset_univ :
        closure (interior (closure A)) ⊆ (Set.univ : Set X) := by
      intro x _; simp
    -- Combine the two inclusions to obtain the equality.
    exact Set.Subset.antisymm h_subset_univ h_univ_subset
  -- Apply the existing lemma turning density of the interior into `P2`.
  exact
    Topology.P2_of_dense_interior (X := X) (A := closure A) h_dense

theorem Topology.closure_interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    closure (interior (closure A)) = closure A := by
  -- First, use the existing lemma giving `interior (closure A) = closure A`.
  have h₁ :
      interior (closure (A : Set X)) = closure A :=
    Topology.interior_closure_eq_closure_of_isOpen_closure
      (X := X) (A := A) h_open
  -- Taking closures of both sides and simplifying yields the desired result.
  calc
    closure (interior (closure (A : Set X))) =
        closure (closure A) := by
          simpa [h₁]
    _ = closure A := by
          simp [closure_closure]

theorem Topology.closure_inter_interior_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) ∩ interior (B : Set X) ⊆ closure (A ∩ B : Set X) := by
  intro x hx
  rcases hx with ⟨h_clA, h_intB⟩
  -- We show that `x` belongs to `closure (A ∩ B)`.
  have : x ∈ closure (A ∩ B : Set X) := by
    -- Use the neighbourhood characterisation of the closure.
    refine (mem_closure_iff.2 ?_)
    intro U hU_open hxU
    -- Consider the open set `U ∩ interior B`, which contains `x`.
    have hV_open : IsOpen (U ∩ interior (B : Set X)) := hU_open.inter isOpen_interior
    have hxV : x ∈ (U ∩ interior (B : Set X)) := And.intro hxU h_intB
    -- Since `x ∈ closure A`, this open set meets `A`.
    have h_nonempty : ((U ∩ interior (B : Set X)) ∩ A).Nonempty := by
      have h_closureA := (mem_closure_iff.1 h_clA)
      exact h_closureA (U ∩ interior (B : Set X)) hV_open hxV
    -- A point in this intersection lies in `U ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyU, hy_intB⟩, hyA⟩⟩
    have hyB : y ∈ (B : Set X) := interior_subset hy_intB
    exact ⟨y, And.intro hyU (And.intro hyA hyB)⟩
  exact this

theorem Topology.isClosed_closure_inter_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    IsClosed ((closure (A : Set X)) ∩ closure B) := by
  have hA : IsClosed (closure (A : Set X)) := isClosed_closure
  have hB : IsClosed (closure (B : Set X)) := isClosed_closure
  exact hA.inter hB

theorem Topology.isOpen_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 (X := X) (closure (A : Set X))) :
    IsOpen (closure A) := by
  exact (Topology.P3_closure_iff_isOpen_closure (X := X) (A := A)).1 h

theorem Topology.closure_image_interior_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {A : Set X} :
    closure (f '' interior A) ⊆ closure (f '' A) := by
  -- The image of `interior A` is contained in the image of `A`.
  have h_image : (f '' interior A : Set Y) ⊆ f '' A := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, interior_subset hx, rfl⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_image

theorem Topology.closure_interior_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simp

theorem Topology.interior_of_open_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : IsOpen (closure (interior (A : Set X)))) :
    interior (closure (interior (A : Set X))) = closure (interior A) := by
  simpa [h.interior_eq]

theorem Topology.closure_inter_interior_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) ∩ interior (closure A) = interior (closure A) := by
  -- `interior (closure A)` is contained in `closure A`.
  have h_subset : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
    interior_subset
  -- Reorder the intersection to apply the lemma, then rewrite back.
  calc
    closure (A : Set X) ∩ interior (closure A)
        = interior (closure A) ∩ closure A := by
          simpa [Set.inter_comm]
    _ = interior (closure A) := by
          exact Set.inter_eq_self_of_subset_left h_subset

theorem Topology.P2_interior_union_interior {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    Topology.P2 (X := X) (interior A ∪ interior B) := by
  -- `P2` holds for the interior of any set.
  have hA : Topology.P2 (X := X) (interior A) :=
    Topology.P2_interior (X := X) (A := A)
  have hB : Topology.P2 (X := X) (interior B) :=
    Topology.P2_interior (X := X) (A := B)
  -- Combine the two instances using the union lemma for `P2`.
  exact
    Topology.P2_union (X := X)
      (A := interior A) (B := interior B) hA hB

theorem Topology.P2_closure_interior_of_isOpen_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (X := X) (closure (interior A)) := by
  -- Use the equivalence previously established for closed sets.
  have h_equiv :=
    Topology.P2_closure_interior_iff_isOpen_closure_interior (X := X) (A := A)
  exact h_equiv.mpr h_open

theorem Topology.closure_subset_closure_left_of_subset_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ closure (B : Set X)) :
    closure (A : Set X) ⊆ closure B := by
  simpa [closure_closure] using closure_mono h

theorem Topology.closure_inter_interiors_subset_inter_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B : Set X) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show membership in `closure (interior A)`.
  have hxA : x ∈ closure (interior A) := by
    -- `interior A ∩ interior B ⊆ interior A`.
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior A := by
      intro y hy; exact hy.1
    -- Apply monotonicity of `closure`.
    exact (closure_mono h_subset) hx
  -- Show membership in `closure (interior B)`.
  have hxB : x ∈ closure (interior B) := by
    -- `interior A ∩ interior B ⊆ interior B`.
    have h_subset : (interior A ∩ interior B : Set X) ⊆ interior B := by
      intro y hy; exact hy.2
    -- Apply monotonicity of `closure`.
    exact (closure_mono h_subset) hx
  -- Combine the two facts.
  exact And.intro hxA hxB

theorem Topology.interior_closure_subset_closure_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (B : Set X)) ⊆ interior (closure (A ∪ B : Set X)) := by
  exact
    Topology.interior_closure_mono
      (X := X) (A := B) (B := A ∪ B)
      (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)

theorem Topology.isClosed_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed (closure (interior (closure (A : Set X)))) := by
  simpa using
    (isClosed_closure :
      IsClosed (closure (interior (closure (A : Set X)))))

theorem Topology.P1_and_empty_interior_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (Topology.P1 (X := X) A ∧ interior (A : Set X) = ∅) ↔ A = ∅ := by
  constructor
  · rintro ⟨hP1, hInt⟩
    -- From `P1` we have `A ⊆ closure (interior A)`.
    have h_sub : (A : Set X) ⊆ (∅ : Set X) := by
      have hA_sub : (A : Set X) ⊆ closure (interior A) := hP1
      simpa [hInt, closure_empty] using hA_sub
    -- The reverse inclusion is trivial.
    have h_empty_sub : (∅ : Set X) ⊆ A := Set.empty_subset _
    -- Conclude the desired equality of sets.
    exact Set.Subset.antisymm h_sub h_empty_sub
  · intro hA
    -- Rewrite everything in terms of `∅`.
    have hP1 : Topology.P1 (X := X) A := by
      simpa [hA] using Topology.P1_empty (X := X)
    have hInt : interior (A : Set X) = (∅ : Set X) := by
      simpa [hA] using (interior_empty : interior (∅ : Set X) = ∅)
    exact And.intro hP1 hInt

theorem Topology.isOpen_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (interior (closure (interior A))) := by
  exact isOpen_interior

theorem Topology.P1_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior A) ↔ Topology.P2 (X := X) (interior A) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := interior A) h_open)

theorem Topology.interior_closure_diff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure A) := by
  -- `A \ B` is contained in `A`.
  have h₁ : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (A \ B : Set X) ⊆ closure A := closure_mono h₁
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono h₂

theorem Topology.isOpen_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    IsOpen (A : Set X) := by
  exact
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP3

theorem Topology.interior_diff_closure_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ closure (B : Set X) : Set X) = interior A \ closure B := by
  have h_closed : IsClosed (closure (B : Set X)) := isClosed_closure
  simpa using
    Topology.interior_diff_closed_eq (X := X) (A := A) (C := closure B) h_closed

theorem Topology.interior_diff_closure_subset_interior_diff {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) \ closure B ⊆ interior (A \ B : Set X) := by
  intro x hx
  rcases hx with ⟨hx_intA, hx_not_clB⟩
  -- Define two auxiliary open sets.
  have hU_open : IsOpen (interior (A : Set X)) := isOpen_interior
  have hV_open : IsOpen ((closure B)ᶜ : Set X) := by
    simpa using (isClosed_closure (A := B)).isOpen_compl
  -- Their intersection is an open neighbourhood of `x`.
  have hW_open :
      IsOpen (interior (A : Set X) ∩ (closure B)ᶜ : Set X) :=
    hU_open.inter hV_open
  have hxW :
      x ∈ (interior (A : Set X) ∩ (closure B)ᶜ : Set X) :=
    And.intro hx_intA hx_not_clB
  -- Show that this neighbourhood is contained in `A \ B`.
  have hW_subset :
      (interior (A : Set X) ∩ (closure B)ᶜ : Set X) ⊆ (A \ B : Set X) := by
    intro y hy
    have hyA : y ∈ A :=
      (interior_subset : interior (A : Set X) ⊆ A) hy.1
    have hy_notB : y ∉ B := by
      intro hBy
      have : y ∈ closure B := subset_closure hBy
      exact hy.2 this
    exact And.intro hyA hy_notB
  -- Apply maximality of the interior to deduce the claim.
  exact
    (interior_maximal hW_subset hW_open) hxW

theorem Topology.P2_iff_P1_and_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) := by
  constructor
  · intro hP2
    -- `P1` follows from `P2` for a closed set.
    have hP1 : Topology.P1 (X := X) A :=
      Topology.P2_implies_P1_of_isClosed (X := X) (A := A) hA hP2
    -- `P3` is equivalent to `P2` for closed sets.
    have hP3 : Topology.P3 (X := X) A := by
      have h_equiv :=
        Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hA
      exact h_equiv.1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨_, hP3⟩
    -- For closed sets, `P3` implies `P2`.
    exact
      Topology.P3_implies_P2_of_isClosed (X := X) (A := A) hA hP3

theorem Topology.P1_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior A) ↔ Topology.P3 (X := X) (interior A) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_iff_P3_of_isOpen (X := X) (A := interior A) h_open)

theorem Topology.interior_inter_closure_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure (B : Set X) : Set X) ⊆
      interior A ∩ interior (closure B) := by
  intro x hx
  -- `x` lies in `interior A`
  have hxA : x ∈ interior A := by
    -- `A ∩ closure B ⊆ A`
    have h₁ : (A ∩ closure (B : Set X) : Set X) ⊆ A :=
      Set.inter_subset_left
    -- Monotonicity of `interior`
    have h₂ :
        interior (A ∩ closure (B : Set X) : Set X) ⊆ interior A :=
      interior_mono h₁
    exact h₂ hx
  -- `x` lies in `interior (closure B)`
  have hxB : x ∈ interior (closure B) := by
    -- `A ∩ closure B ⊆ closure B`
    have h₁ : (A ∩ closure (B : Set X) : Set X) ⊆ closure B :=
      Set.inter_subset_right
    -- Monotonicity of `interior`
    have h₂ :
        interior (A ∩ closure (B : Set X) : Set X) ⊆
          interior (closure B) :=
      interior_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_iter_four_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure (A : Set X)))))))) =
      interior (closure A) := by
  simpa [Topology.interior_closure_iter_three_eq (X := X) (A := A),
        Topology.interior_closure_interior_closure_eq (X := X) (A := A)]

theorem Topology.P3_iff_P1_and_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A) := by
  constructor
  · intro hP3
    -- `P1` follows from `P3` for a closed set.
    have hP1 : Topology.P1 (X := X) A :=
      Topology.P3_implies_P1_of_isClosed (X := X) (A := A) hA hP3
    -- `P2` also follows from `P3` for a closed set.
    have hP2 : Topology.P2 (X := X) A :=
      Topology.P3_implies_P2_of_isClosed (X := X) (A := A) hA hP3
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    -- `P2` always implies `P3`.
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2

theorem Topology.P2_and_empty_interior_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (Topology.P2 (X := X) A ∧ interior (A : Set X) = ∅) ↔ A = ∅ := by
  constructor
  · rintro ⟨hP2, hInt⟩
    -- From `P2`, we have the inclusion `A ⊆ interior (closure (interior A))`.
    have h_subset : (A : Set X) ⊆ interior (closure (interior A)) := hP2
    -- Since `interior A = ∅`, the right‐hand side is `∅`.
    have h_eq : interior (closure (interior A)) = (∅ : Set X) := by
      simpa [hInt, closure_empty, interior_empty]
    -- Hence `A ⊆ ∅`, so `A = ∅`.
    have h_empty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [h_eq] using h_subset
    exact Set.Subset.antisymm h_empty (Set.empty_subset _)
  · intro hA
    -- If `A = ∅`, both required conditions are immediate.
    have hP2 : Topology.P2 (X := X) A := by
      simpa [hA] using Topology.P2_empty (X := X)
    have hInt : interior (A : Set X) = (∅ : Set X) := by
      simpa [hA] using (interior_empty : interior (∅ : Set X) = ∅)
    exact And.intro hP2 hInt

theorem Topology.P2_of_P1_and_isOpen_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A)
    (h_open : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (X := X) A := by
  -- Unfold `P2` to obtain the required subset relation.
  dsimp [Topology.P2] at *
  intro x hxA
  -- From `P1`, `x` lies in the closure of the interior of `A`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Since this closure is open, its interior is itself.
  have h_eq : interior (closure (interior (A : Set X))) =
      closure (interior A) := by
    simpa [h_open.interior_eq]
  -- Reinterpret the membership via the set equality.
  simpa [h_eq] using hx_cl

theorem Topology.image_closure_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {A : Set X} :
    f '' closure (A : Set X) ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hx_cl, rfl⟩
  -- We show `f x ∈ closure (f '' A)` using the neighbourhood
  -- characterisation of the closure.
  have : f x ∈ closure (f '' A) := by
    -- `mem_closure_iff` reduces the goal to exhibiting, for every
    -- neighbourhood `V` of `f x`, a point of `f '' A` lying in `V`.
    apply (mem_closure_iff).2
    intro V hV_open hxV
    -- The preimage of `V` under `f` is an open neighbourhood of `x`.
    have hU_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
    have hxU : x ∈ f ⁻¹' V := by
      simpa using hxV
    -- Since `x` belongs to the closure of `A`, this neighbourhood
    -- meets `A` non‐trivially.
    have h_nonempty : ((f ⁻¹' V) ∩ A).Nonempty := by
      -- Apply the defining property of membership in the closure.
      have h_closure := (mem_closure_iff).1 hx_cl
      have h := h_closure (f ⁻¹' V) hU_open hxU
      simpa [Set.inter_comm] using h
    -- Map the witness through `f` to obtain the required point in `V ∩ f '' A`.
    rcases h_nonempty with ⟨z, ⟨hzU, hzA⟩⟩
    -- `f z` lies in `V` by construction …
    have hzV : f z ∈ V := by
      have : z ∈ f ⁻¹' V := hzU
      simpa using this
    -- … and in `f '' A` since `z ∈ A`.
    have hz_image : f z ∈ f '' A := ⟨z, hzA, rfl⟩
    exact ⟨f z, And.intro hzV hz_image⟩
  simpa using this

theorem Topology.interior_compl_inter_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ : Set X) ∩ closure (A : Set X) = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hx_int, hx_cl⟩
    -- Use the neighbourhood formulation of `closure` with the open set
    -- `interior (Aᶜ)`, which contains `x`.
    have h_false : False := by
      rcases (mem_closure_iff).1 hx_cl
          (interior (Aᶜ : Set X)) isOpen_interior hx_int with
        ⟨y, hy_int, hyA⟩
      -- But `y ∈ interior (Aᶜ)` implies `y ∉ A`, contradicting `hyA`.
      have : y ∈ (Aᶜ : Set X) := interior_subset hy_int
      exact this hyA
    exact False.elim h_false
  · intro x hx
    cases hx

theorem Topology.P1_union_interior_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (A ∪ interior B) := by
  -- `P1` holds for `interior B` because the interior of any set is open.
  have hB : Topology.P1 (X := X) (interior B) :=
    Topology.P1_interior (X := X) (A := B)
  -- Combine the two `P1` properties using the existing union lemma.
  simpa using
    Topology.P1_union (X := X) (A := A) (B := interior B) hA hB

theorem Topology.P3_and_empty_interior_closure_iff_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (Topology.P3 (X := X) A ∧ interior (closure (A : Set X)) = ∅) ↔ A = ∅ := by
  constructor
  · rintro ⟨hP3, hInt⟩
    -- From `P3`, we have `A ⊆ interior (closure A)`.
    have h_sub : (A : Set X) ⊆ interior (closure A) := hP3
    -- Using the hypothesis `interior (closure A) = ∅`, we deduce `A ⊆ ∅`.
    have h_empty : (A : Set X) ⊆ (∅ : Set X) := by
      simpa [hInt] using h_sub
    -- Combine with the trivial inclusion `∅ ⊆ A` to get the desired equality.
    exact Set.Subset.antisymm h_empty (Set.empty_subset _)
  · intro hA
    -- Rewrite everything in terms of `∅`.
    have hP3 : Topology.P3 (X := X) A := by
      simpa [hA] using Topology.P3_empty (X := X)
    have hInt : interior (closure (A : Set X)) = (∅ : Set X) := by
      simpa [hA] using Topology.interior_closure_empty (X := X)
    exact And.intro hP3 hInt

theorem Topology.interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  -- From the density of `interior A` we already know `closure A = univ`.
  have h_closure_univ :
      closure (A : Set X) = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (X := X) (A := A) hA
  -- Rewrite and simplify using `interior_univ`.
  simpa [h_closure_univ, interior_univ]

theorem Topology.image_interior_subset_closure_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {A : Set X} :
    f '' interior (A : Set X) ⊆ closure (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hx_int, rfl⟩
  have hxA : (x : X) ∈ (A : Set X) := interior_subset hx_int
  have h_im : (f x) ∈ f '' (A : Set X) := ⟨x, hxA, rfl⟩
  exact subset_closure h_im

theorem Topology.P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (closure (A ∪ B : Set X)) := by
  -- First, `P1` holds for the union `A ∪ B`.
  have hUnion : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Then, upgrade the property to the closure of the union.
  exact
    Topology.P1_closure_of_P1 (X := X) (A := A ∪ B) hUnion

theorem Topology.image_subset_closure_image_interior_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P1 (X := X) A) :
    f '' (A : Set X) ⊆ closure (f '' interior A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- From `P1`, `x` lies in the closure of `interior A`.
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- Hence `f x` lies in `f '' closure (interior A)`.
  have hy_image : f x ∈ f '' closure (interior A) := ⟨x, hx_cl, rfl⟩
  -- Use continuity of `f` to pass from the image of a closure
  -- to the closure of an image.
  have h_subset : f '' closure (interior A) ⊆ closure (f '' interior A) :=
    image_closure_subset_closure_image (X := X) (Y := Y)
      (f := f) hf (A := interior A)
  exact h_subset hy_image

theorem Topology.interior_eq_compl_closure_compl {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (A : Set X) = (closure ((A : Set X)ᶜ))ᶜ := by
  simpa [compl_compl] using (interior_compl (s := (Aᶜ : Set X)))

theorem Topology.P1_of_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1]
  intro x _
  -- Since `interior A = univ`, its closure is also `univ`, so every point belongs to it.
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h, closure_univ] using this

theorem Topology.interior_compl_eq_compl_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := by
  simpa using interior_compl (A := A)

theorem Topology.interior_union_three_eq_self_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) (hC : IsOpen (C : Set X)) :
    interior (A ∪ B ∪ C : Set X) = A ∪ B ∪ C := by
  -- The union of three open sets is open.
  have h_open : IsOpen (A ∪ B ∪ C : Set X) := (hA.union hB).union hC
  -- For an open set `U`, `interior U = U`.
  simpa using h_open.interior_eq

theorem Topology.preimage_closure_subset_closure_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set Y} :
    closure (f ⁻¹' A) ⊆ f ⁻¹' closure A := by
  intro x hx
  -- We show `f x ∈ closure A` using the neighbourhood
  -- characterisation of the closure.
  have h_fx : f x ∈ closure A := by
    -- Apply `mem_closure_iff` at `f x`.
    apply (mem_closure_iff).2
    intro V hV_open h_fxV
    -- Consider the open neighbourhood `f ⁻¹' V` of `x`.
    have hU_open : IsOpen (f ⁻¹' V) := hV_open.preimage hf
    have hxU : x ∈ f ⁻¹' V := by
      simpa using h_fxV
    -- Since `x ∈ closure (f ⁻¹' A)`, this neighbourhood meets
    -- `f ⁻¹' A` non‐trivially.
    have h_nonempty : ((f ⁻¹' V) ∩ f ⁻¹' A).Nonempty := by
      have := (mem_closure_iff).1 hx (f ⁻¹' V) hU_open hxU
      simpa [Set.preimage_inter] using this
    -- Map a witnessing point through `f` to obtain a point in `V ∩ A`.
    rcases h_nonempty with ⟨y, hyV, hyA⟩
    have hyV' : f y ∈ V := by
      simpa using hyV
    have hyA' : f y ∈ A := by
      simpa using hyA
    exact ⟨f y, And.intro hyV' hyA'⟩
  -- Reinterpret the membership in terms of the preimage.
  simpa using h_fx

theorem Topology.P3_union_interior_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (interior A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.P3_union_interior_right (X := X) (A := B) (B := A) hB)

theorem Topology.P1_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Topology.P1 (X := X) A) (hU : IsOpen (U : Set X)) :
    Topology.P1 (X := X) (A ∪ U) := by
  -- `P1` holds for the open set `U`.
  have hU_P1 : Topology.P1 (X := X) U :=
    Topology.isOpen_P1 (X := X) (A := U) hU
  -- Combine the two `P1` properties via the union lemma.
  exact Topology.P1_union (X := X) (A := A) (B := U) hA hU_P1

theorem Topology.P1_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen (U : Set X)) (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (U ∪ A) := by
  -- `P1` holds automatically for an open set.
  have hU_P1 : Topology.P1 (X := X) U :=
    Topology.isOpen_P1 (X := X) (A := U) hU
  -- Combine the two `P1` properties using the union lemma.
  simpa [Set.union_comm] using
    Topology.P1_union (X := X) (A := A) (B := U) hA hU_P1

theorem Topology.interior_eq_closure_inter_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) = closure A ∩ interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in `A`, hence in `closure A`
    have hxA : x ∈ (A : Set X) := interior_subset hx
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    exact And.intro hx_cl hx
  · intro x hx
    exact hx.2



theorem Topology.closure_subset_closure_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ closure (interior B)) :
    closure (A : Set X) ⊆ closure (interior B) := by
  -- Taking closures preserves the given inclusion.
  have h₁ : closure (A : Set X) ⊆ closure (closure (interior B)) :=
    closure_mono h
  -- Simplify the right‐hand side using idempotence of `closure`.
  simpa [closure_closure] using h₁

theorem Topology.P2_of_isClosed_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    Topology.P2 (X := X) A := by
  -- Obtain the triple property for sets that are both closed and open.
  have h := Topology.P1_P2_P3_of_isClosed_isOpen (X := X) (A := A) h_closed h_open
  -- Extract the `P2` component from the conjunction.
  exact h.2.1



theorem Topology.preimage_interior_subset_interior_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {B : Set Y} :
    f ⁻¹' interior (B : Set Y) ⊆ interior (f ⁻¹' B) := by
  -- The preimage of an open set under a continuous map is open.
  have h_open : IsOpen (f ⁻¹' interior (B : Set Y)) := by
    have : IsOpen (interior (B : Set Y)) := isOpen_interior
    exact this.preimage hf
  -- `f ⁻¹' interior B` is contained in `f ⁻¹' B` since `interior B ⊆ B`.
  have h_subset :
      (f ⁻¹' interior (B : Set Y)) ⊆ f ⁻¹' B :=
    Set.preimage_mono (interior_subset : interior (B : Set Y) ⊆ B)
  -- Apply the maximality of the interior for the open set `f ⁻¹' interior B`.
  intro x hx
  exact (interior_maximal h_subset h_open) hx

theorem Topology.P2_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2
  · intro _
    exact Topology.P2_of_dense_interior (X := X) (A := A) h_dense

theorem Topology.interior_closure_inter_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    interior (closure (A ∩ B : Set X)) = interior (A ∩ B) := by
  -- The intersection of two closed sets is closed.
  have h_closed : IsClosed (A ∩ B : Set X) := hA.inter hB
  -- Apply the existing lemma for closed sets.
  simpa using
    Topology.interior_closure_eq_interior_of_isClosed
      (X := X) (A := (A ∩ B)) h_closed

theorem Topology.interior_inter_closure_compl_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ∩ closure (Aᶜ : Set X) = (∅ : Set X) := by
  simpa [compl_compl] using
    (Topology.interior_compl_inter_closure_eq_empty (X := X) (A := Aᶜ))

theorem Topology.P1_closure_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (closure A ∪ closure B) := by
  -- Step 1: `P1` holds for `A ∪ B`.
  have hUnion : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Step 2: upgrade to `P1` for the closure of the union.
  have hClosureUnion : Topology.P1 (X := X) (closure (A ∪ B)) :=
    Topology.P1_closure_of_P1 (X := X) (A := A ∪ B) hUnion
  -- Step 3: identify the goal set via `closure_union`.
  have h_eq :
      (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
    simpa [closure_union]
  -- Step 4: unfold the goal and transport memberships through the equality.
  dsimp [Topology.P1] at hClosureUnion ⊢
  intro x hx
  -- Convert membership in `closure A ∪ closure B` to membership in `closure (A ∪ B)`.
  have hx_closure : x ∈ closure (A ∪ B : Set X) := by
    have : x ∈ (closure (A : Set X) ∪ closure (B : Set X)) := hx
    simpa [h_eq] using this
  -- Apply `P1` for `closure (A ∪ B)`.
  have hx_goal :
      x ∈ closure (interior (closure (A ∪ B : Set X))) :=
    hClosureUnion hx_closure
  -- Rewrite the target set back to the desired one.
  have h_int_eq :
      interior (closure (A ∪ B : Set X)) =
        interior (closure (A : Set X) ∪ closure (B : Set X)) := by
    simpa [h_eq]
  simpa [h_int_eq] using hx_goal

theorem Topology.interior_closure_interior_inter_eq
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B : Set X))) =
      interior (closure (interior A ∩ interior B)) := by
  have h : interior (A ∩ B : Set X) = interior A ∩ interior B := by
    simpa using Topology.interior_inter_eq (X := X) (A := A) (B := B)
  simpa [h]

theorem Topology.closure_interior_compl_eq_compl_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (Aᶜ : Set X)) = (interior (closure (A : Set X)))ᶜ := by
  -- First rewrite `interior (Aᶜ)` using the complement–closure duality.
  have h₁ :
      interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  -- Apply `closure` to both sides and simplify using `closure_compl`.
  calc
    closure (interior (Aᶜ : Set X))
        = closure ((closure (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (interior (closure (A : Set X)))ᶜ := by
          simpa using closure_compl (s := closure (A : Set X))

theorem Topology.closure_interior_union_three_eq_closure_union_interiors
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ∪ closure (interior C) =
      closure (interior A ∪ interior B ∪ interior C) := by
  -- First, regroup the unions for convenient rewriting.
  calc
    closure (interior A) ∪ closure (interior B) ∪ closure (interior C)
        = closure (interior A) ∪ (closure (interior B) ∪ closure (interior C)) := by
          simp [Set.union_assoc]
    _ = closure (interior A) ∪ closure (interior B ∪ interior C) := by
          -- Use the two‐set equality on the last two terms.
          simpa using
            congrArg (fun s : Set X ↦ closure (interior A) ∪ s)
              (closure_union (interior (B : Set X)) (interior C))
    _ = closure (interior A ∪ (interior B ∪ interior C)) := by
          -- Apply the two‐set equality again.
          simpa using
            (closure_union (interior (A : Set X)) (interior B ∪ interior C)).symm
    _ = closure (interior A ∪ interior B ∪ interior C) := by
          simpa [Set.union_assoc]

theorem Topology.P2_iff_P1_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P1 (X := X) A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1 (X := X) (A := A) hP2
  · intro _
    exact Topology.P2_of_dense_interior (X := X) (A := A) h_dense

theorem Topology.interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure A) := by
  -- We prove the two inclusions separately and conclude by extensionality.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    -- First, note `interior (closure A) ⊆ closure A`.
    have h₁ :
        (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    -- Taking closures preserves inclusions.
    have h₂ :
        closure (interior (closure (A : Set X))) ⊆
          closure (closure (A : Set X)) :=
      closure_mono h₁
    -- Simplify `closure (closure A)` and apply monotonicity of `interior`.
    have h₃ :
        closure (interior (closure (A : Set X))) ⊆ closure A := by
      simpa [closure_closure] using h₂
    -- Finally, `interior` is monotone.
    exact interior_mono h₃
  · -- `⊇` direction
    -- The set `interior (closure A)` is open …
    have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- … and contained in `closure (interior (closure A))`.
    have h_subset :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) :=
      subset_closure
    -- By maximality of the interior of an open set, it is contained in the
    -- interior of any superset—here `closure (interior (closure A))`.
    have h_interior :
        interior (closure (A : Set X)) ⊆
          interior (closure (interior (closure A))) :=
      interior_maximal h_subset h_open
    -- This is exactly the desired inclusion.
    simpa using h_interior

theorem Topology.P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro _hP1
    exact Topology.P3_of_dense_interior (X := X) (A := A) h_dense
  · intro _hP3
    exact Topology.P1_of_dense_interior (X := X) (A := A) h_dense

theorem Topology.P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P2 (X := X) A) (hB : Topology.P2 (X := X) B)
    (hC : Topology.P2 (X := X) C) (hD : Topology.P2 (X := X) D) :
    Topology.P2 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First, unite the three sets `A`, `B`, and `C`.
  have hABC : Topology.P2 (X := X) (A ∪ B ∪ C) :=
    Topology.P2_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Next, union the resulting set with `D`.
  have hABCD : Topology.P2 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P2_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Rewrite the unions to match the desired normal form.
  simpa [Set.union_assoc, Set.union_left_comm, Set.union_right_comm] using hABCD

theorem Topology.P2_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (closure (A : Set X))) ↔
      Topology.P2 (X := X) (closure A) := by
  simpa [closure_closure]

theorem Topology.interior_closure_interior_closure_eq_of_P1 {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (X := X) A) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  -- First, upgrade `P1` from `A` to `closure A`.
  have h_closure : Topology.P1 (X := X) (closure A) :=
    Topology.P1_closure_of_P1 (X := X) (A := A) hA
  -- Apply the existing equality for sets satisfying `P1`.
  have h_eq :
      interior (closure (closure (A : Set X))) =
        interior (closure (interior (closure A))) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P1
      (X := X) (A := closure A) h_closure
  -- Simplify the left‐hand side and reorient the equality.
  simpa [closure_closure] using h_eq.symm

theorem Topology.isOpen_closure_iff_interior_closure_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔ interior (closure (A : Set X)) = closure A := by
  constructor
  · intro h_open
    exact
      Topology.interior_closure_eq_closure_of_isOpen_closure
        (X := X) (A := A) h_open
  · intro h_eq
    have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [h_eq] using this

theorem Topology.closure_compl_eq_compl_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
  simpa using closure_compl (A := A)

theorem Topology.P1_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B)
    (hC : Topology.P1 (X := X) C) (hD : Topology.P1 (X := X) D) :
    Topology.P1 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First, combine `A`, `B`, and `C`.
  have hABC : Topology.P1 (X := X) (A ∪ B ∪ C) :=
    Topology.P1_union_three (X := X) (A := A) (B := B) (C := C) hA hB hC
  -- Then, union the result with `D`.
  have hABCD : Topology.P1 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P1_union (X := X) (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Reassociate the unions to match the desired form.
  simpa [Set.union_assoc] using hABCD

theorem Topology.P3_union_four {X : Type*} [TopologicalSpace X]
    {A B C D : Set X}
    (hA : Topology.P3 (X := X) A)
    (hB : Topology.P3 (X := X) B)
    (hC : Topology.P3 (X := X) C)
    (hD : Topology.P3 (X := X) D) :
    Topology.P3 (X := X) (A ∪ B ∪ C ∪ D) := by
  -- First union `A` and `B`.
  have hAB : Topology.P3 (X := X) (A ∪ B) :=
    Topology.P3_union (X := X) (A := A) (B := B) hA hB
  -- Then add `C`.
  have hABC : Topology.P3 (X := X) (A ∪ B ∪ C) := by
    -- `(A ∪ B ∪ C)` is definitionally `(A ∪ B) ∪ C`.
    have : Topology.P3 (X := X) ((A ∪ B) ∪ C) :=
      Topology.P3_union (X := X) (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Finally, add `D`.
  have hABCD : Topology.P3 (X := X) ((A ∪ B ∪ C) ∪ D) :=
    Topology.P3_union (X := X) (A := (A ∪ B ∪ C)) (B := D) hABC hD
  -- Rewrite to the desired union ordering.
  simpa [Set.union_assoc] using hABCD

theorem Topology.P1_P2_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior A) ∧
      Topology.P2 (X := X) (interior A) ∧
      Topology.P3 (X := X) (interior A) := by
  -- `interior A` is an open set.
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  -- Hence all three properties hold by the existing lemma for open sets.
  simpa using
    Topology.P1_P2_P3_of_isOpen (X := X) (A := interior A) h_open

theorem IsOpen.compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsOpen (s : Set X)) :
    IsClosed ((s : Set X)ᶜ) := by
  simpa using h.isClosed_compl

theorem IsClosed.compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsClosed (s : Set X)) :
    IsOpen ((s : Set X)ᶜ) := by
  simpa using h.isOpen_compl

theorem Topology.closure_interior_closure_inter_subset_inter_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∩ B : Set X))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- Membership in `closure (interior (closure A))`
  have hxA : x ∈ closure (interior (closure A)) := by
    -- `closure (A ∩ B) ⊆ closure A`
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    -- Hence, by monotonicity, `interior (closure (A ∩ B)) ⊆ interior (closure A)`.
    have h₂ :
        (interior (closure (A ∩ B : Set X)) : Set X) ⊆
          interior (closure A) :=
      interior_mono h₁
    -- Taking closures preserves the inclusion.
    have h₃ :
        closure (interior (closure (A ∩ B : Set X))) ⊆
          closure (interior (closure A)) :=
      closure_mono h₂
    exact h₃ hx
  -- Membership in `closure (interior (closure B))`
  have hxB : x ∈ closure (interior (closure B)) := by
    -- `closure (A ∩ B) ⊆ closure B`
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    -- Monotone behaviour of `interior`.
    have h₂ :
        (interior (closure (A ∩ B : Set X)) : Set X) ⊆
          interior (closure B) :=
      interior_mono h₁
    -- Take closures to finish.
    have h₃ :
        closure (interior (closure (A ∩ B : Set X))) ⊆
          closure (interior (closure B)) :=
      closure_mono h₂
    exact h₃ hx
  exact And.intro hxA hxB

theorem Topology.interior_closure_compl_eq_compl_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (Aᶜ : Set X)) = (closure (interior (A : Set X)))ᶜ := by
  -- First, rewrite `closure (Aᶜ)` using the complement–interior duality.
  have h₁ : (closure (Aᶜ : Set X)) = (interior (A : Set X))ᶜ := by
    simpa using
      (Topology.closure_compl_eq_compl_interior (X := X) (A := A))
  -- Apply the same duality to `interior ((interior A)ᶜ)`.
  calc
    interior (closure (Aᶜ : Set X))
        = interior ((interior (A : Set X))ᶜ) := by
          simpa [h₁]
    _ = (closure (interior (A : Set X)))ᶜ := by
          simpa using
            (Topology.interior_compl_eq_compl_closure
              (X := X) (A := interior A))

theorem IsOpen.sUnion {X : Type*} [TopologicalSpace X] {F : Set (Set X)}
    (hF : ∀ A : Set X, A ∈ F → IsOpen (A : Set X)) :
    IsOpen (⋃₀ F : Set X) := by
  simpa using isOpen_sUnion (X := X) hF

theorem Topology.P3_interior_union_interior {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P3 (X := X) (interior A ∪ interior B) := by
  -- `P3` holds for the interior of any set.
  have hA : Topology.P3 (X := X) (interior A) :=
    Topology.P3_interior (X := X) (A := A)
  have hB : Topology.P3 (X := X) (interior B) :=
    Topology.P3_interior (X := X) (A := B)
  -- Combine the two `P3` properties using the union lemma.
  exact
    Topology.P3_union (X := X)
      (A := interior A) (B := interior B) hA hB

theorem Topology.interior_inter_closure_subset_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∩ closure (B : Set X) ⊆ closure (A ∩ B : Set X) := by
  intro x hx
  rcases hx with ⟨hx_intA, hx_clB⟩
  -- We prove that every open neighbourhood of `x` intersects `A ∩ B`.
  have : x ∈ closure (A ∩ B : Set X) := by
    apply (mem_closure_iff).2
    intro V hV_open hxV
    -- Consider the open neighbourhood `V ∩ interior A` of `x`.
    have hU_open : IsOpen (V ∩ interior (A : Set X)) :=
      hV_open.inter isOpen_interior
    have hxU : x ∈ V ∩ interior (A : Set X) := ⟨hxV, hx_intA⟩
    -- Since `x ∈ closure B`, this neighbourhood meets `B`.
    have h_nonempty :
        ((V ∩ interior (A : Set X)) ∩ B).Nonempty :=
      (mem_closure_iff).1 hx_clB (V ∩ interior (A : Set X)) hU_open hxU
    -- Extract a witness and show it lies in `V ∩ (A ∩ B)`.
    rcases h_nonempty with ⟨y, ⟨⟨hyV, hy_intA⟩, hyB⟩⟩
    have hyA : y ∈ A := interior_subset hy_intA
    exact ⟨y, ⟨hyV, ⟨hyA, hyB⟩⟩⟩
  exact this

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : closure (A : Set X) = (Set.univ : Set X)) :
    interior (Aᶜ : Set X) = (∅ : Set X) := by
  -- We first show that `interior (Aᶜ)` is contained in `∅`.
  have h_subset : (interior (Aᶜ : Set X)) ⊆ (∅ : Set X) := by
    intro x hx_int
    -- We will derive a contradiction from the assumption that
    -- `x ∈ interior (Aᶜ)`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := by
      -- Since `closure A = univ`, every point lies in `closure A`.
      simpa [hA] using (by
        have : (x : X) ∈ (Set.univ : Set X) := by simp
        exact this)
    -- Use the neighbourhood characterisation of the closure with the open set
    -- `interior (Aᶜ)`, which contains `x`.
    have h_nonempty :
        ((interior (Aᶜ : Set X)) ∩ A).Nonempty :=
      (mem_closure_iff).1 hx_closure (interior (Aᶜ : Set X))
        isOpen_interior hx_int
    rcases h_nonempty with ⟨y, ⟨hy_int, hyA⟩⟩
    -- But `y ∈ interior (Aᶜ)` implies `y ∉ A`, contradicting `hyA`.
    have : (y : X) ∈ (Aᶜ : Set X) := interior_subset hy_int
    exact (this hyA).elim
  -- The reverse inclusion `∅ ⊆ interior (Aᶜ)` is trivial.
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)

theorem Topology.closure_iUnion_interior_subset_closure_iUnion
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    closure (⋃ i, interior (A i) : Set X) ⊆
      closure (⋃ i, A i) := by
  -- The union of the interiors is contained in the union of the sets themselves.
  have h_subset :
      (⋃ i, interior (A i) : Set X) ⊆ ⋃ i, A i := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx_int⟩
    have hxAi : x ∈ A i :=
      (interior_subset : interior (A i) ⊆ A i) hx_int
    exact Set.mem_iUnion.2 ⟨i, hxAi⟩
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset



theorem Topology.closure_union_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    closure (A ∪ B ∪ C : Set X) = closure A ∪ closure B ∪ closure C := by
  simpa [Set.union_assoc] using
    calc
      closure (A ∪ B ∪ C : Set X)
          = closure (A ∪ B) ∪ closure C := by
              simpa [Set.union_assoc] using closure_union (A ∪ B) C
      _ = (closure A ∪ closure B) ∪ closure C := by
              simpa using
                congrArg (fun s : Set X => s ∪ closure C) (closure_union A B)

theorem Topology.closure_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (A : Set X)) = closure A := by
  simpa [closure_closure]

theorem Topology.interior_inter_three_eq {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior (A ∩ B ∩ C : Set X) =
      interior A ∩ interior B ∩ interior C := by
  -- We prove the two inclusions separately and finish with antisymmetry.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hx
    -- `x ∈ interior A`
    have hxA : x ∈ interior A := by
      have h_sub : (A ∩ B ∩ C : Set X) ⊆ A := by
        intro y hy; exact hy.1.1
      exact (interior_mono h_sub) hx
    -- `x ∈ interior B`
    have hxB : x ∈ interior B := by
      have h_sub : (A ∩ B ∩ C : Set X) ⊆ B := by
        intro y hy; exact hy.1.2
      exact (interior_mono h_sub) hx
    -- `x ∈ interior C`
    have hxC : x ∈ interior C := by
      have h_sub : (A ∩ B ∩ C : Set X) ⊆ C := by
        intro y hy; exact hy.2
      exact (interior_mono h_sub) hx
    exact And.intro (And.intro hxA hxB) hxC
  · -- `⊇` direction
    intro x hx
    rcases hx with ⟨⟨hxA, hxB⟩, hxC⟩
    -- The open set `interior A ∩ interior B ∩ interior C`
    -- will witness that `x` is in the interior of `A ∩ B ∩ C`.
    have h_open :
        IsOpen (interior A ∩ interior B ∩ interior C : Set X) := by
      have hAB :
          IsOpen (interior A ∩ interior B : Set X) :=
        (isOpen_interior : IsOpen (interior A)).inter
          (isOpen_interior : IsOpen (interior B))
      exact hAB.inter (isOpen_interior : IsOpen (interior C))
    -- This open set is contained in `A ∩ B ∩ C`.
    have h_subset :
        (interior A ∩ interior B ∩ interior C : Set X) ⊆
          A ∩ B ∩ C := by
      intro y hy
      have hyA : y ∈ A := interior_subset hy.1.1
      have hyB : y ∈ B := interior_subset hy.1.2
      have hyC : y ∈ C := interior_subset hy.2
      exact And.intro (And.intro hyA hyB) hyC
    -- `x` belongs to the open set.
    have hx_open :
        x ∈ (interior A ∩ interior B ∩ interior C : Set X) :=
      And.intro (And.intro hxA hxB) hxC
    -- Hence `x` belongs to the interior of `A ∩ B ∩ C`.
    have h_mem :
        x ∈ interior (A ∩ B ∩ C : Set X) :=
      (interior_maximal h_subset h_open) hx_open
    exact h_mem

theorem Topology.interior_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A := by
  exact interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)

theorem Topology.image_interior_subset_image_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    {A : Set X} :
    f '' interior (A : Set X) ⊆ f '' closure A := by
  intro y hy
  rcases hy with ⟨x, hx_int, rfl⟩
  -- From `x ∈ interior A` we obtain `x ∈ A`.
  have hxA : (x : X) ∈ A := interior_subset hx_int
  -- Hence `x ∈ closure A`.
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  exact ⟨x, hx_cl, rfl⟩

theorem Topology.closure_image_subset_closure_image_interior_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P1 (X := X) A) :
    closure (f '' A) ⊆ closure (f '' interior A) := by
  -- First, show that every point of `f '' A` already lies in
  -- `closure (f '' interior A)`.
  have h_subset : f '' A ⊆ closure (f '' interior A) := by
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    -- From `P1`, `x` is in the closure of `interior A`.
    have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
    -- Hence `f x` is in `f '' closure (interior A)`.
    have h_fx : f x ∈ f '' closure (interior A) := ⟨x, hx_cl, rfl⟩
    -- Use continuity to pass from `f '' closure _` to `closure (f '' _)`.
    have h_image :
        f '' closure (interior A) ⊆ closure (f '' interior A) :=
      Topology.image_closure_subset_closure_image
        (X := X) (Y := Y) (f := f) hf (A := interior A)
    exact h_image h_fx
  -- Taking closures of both sides gives the required inclusion.
  -- We use a small rewriting step to avoid the double‐closure on the right.
  have : closure (f '' A) ⊆ closure (closure (f '' interior A)) :=
    closure_mono h_subset
  simpa [closure_closure] using this

theorem Topology.interior_inter_subset_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior B := by
  exact interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)

theorem Topology.P3_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hA : Topology.P3 (X := X) A) (hU : IsOpen (U : Set X)) :
    Topology.P3 (X := X) (A ∪ U) := by
  -- `P3` holds for the open set `U`.
  have hU_P3 : Topology.P3 (X := X) U :=
    Topology.isOpen_P3 (X := X) (A := U) hU
  -- Combine the two `P3` properties via the union lemma.
  simpa using
    Topology.P3_union (X := X) (A := A) (B := U) hA hU_P3

theorem Topology.closure_image_eq_closure_image_interior_of_P1
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P1 (X := X) A) :
    closure (f '' A) = closure (f '' interior A) := by
  -- One inclusion is provided by an existing lemma.
  have h₁ :
      closure (f '' A) ⊆ closure (f '' interior A) :=
    Topology.closure_image_subset_closure_image_interior_of_P1
      (X := X) (Y := Y) (f := f) hf (A := A) hA
  -- The reverse inclusion follows from `interior A ⊆ A`.
  have h₂ :
      closure (f '' interior A) ⊆ closure (f '' A) := by
    -- First, relate the underlying images.
    have h_sub : (f '' interior A : Set Y) ⊆ f '' A := by
      intro y hy
      rcases hy with ⟨x, hx_int, rfl⟩
      exact ⟨x, interior_subset hx_int, rfl⟩
    -- Taking closures preserves inclusions.
    exact closure_mono h_sub
  -- Combine the two inclusions to obtain equality.
  exact Set.Subset.antisymm h₁ h₂

theorem Topology.closure_image_eq_closure_image_interior_of_P2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) {A : Set X} (hA : Topology.P2 (X := X) A) :
    closure (f '' (A : Set X)) = closure (f '' interior A) := by
  -- First, upgrade the assumption `P2 A` to `P1 A`.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hA
  -- Invoke the existing equality for sets satisfying `P1`.
  exact
    Topology.closure_image_eq_closure_image_interior_of_P1
      (X := X) (Y := Y) (f := f) hf (A := A) hP1

theorem Topology.interior_compl_union_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (Aᶜ : Set X) ∪ closure (A : Set X) = (Set.univ : Set X) := by
  -- Rewrite `interior (Aᶜ)` as the complement of `closure A`.
  have h : interior (Aᶜ : Set X) = (closure (A : Set X))ᶜ := by
    simpa using
      (Topology.interior_compl_eq_compl_closure (X := X) (A := A))
  -- Use the complement law `sᶜ ∪ s = univ`.
  calc
    interior (Aᶜ : Set X) ∪ closure (A : Set X)
        = (closure (A : Set X))ᶜ ∪ closure A := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simp

theorem Topology.interior_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  -- Express `closure (Aᶜ)` as the complement of `interior A`.
  have h : closure ((A : Set X)ᶜ) = (interior (A : Set X))ᶜ := by
    simpa using Topology.closure_compl_eq_compl_interior (X := X) (A := A)
  -- Substitute and apply the union–complement law.
  calc
    interior (A : Set X) ∪ closure ((A : Set X)ᶜ)
        = interior (A : Set X) ∪ (interior (A : Set X))ᶜ := by
          simpa [h]
    _ = (Set.univ : Set X) := by
          simpa using Set.union_compl_self (interior (A : Set X))

theorem Topology.P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  -- Both `P1` and `P2` hold unconditionally under the density assumption.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) h_dense
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h_dense
  -- Assemble the equivalence from the two unconditional facts.
  constructor
  · intro _; exact hP2
  · intro _; exact hP1

theorem Topology.isClosed_closure_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    IsClosed (closure (A : Set X) ∩ closure (interior B)) := by
  -- Both factors of the intersection are closed.
  have hA : IsClosed (closure (A : Set X)) := isClosed_closure
  have hB : IsClosed (closure (interior (B : Set X))) := isClosed_closure
  -- The intersection of two closed sets is closed.
  exact hA.inter hB

theorem Topology.P3_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (closure (A : Set X))) ↔
      Topology.P3 (X := X) (closure A) := by
  simpa [closure_closure]

theorem Topology.isClosed_interior_iff_closure_interior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed (interior (A : Set X)) ↔ closure (interior A) = interior A := by
  constructor
  · intro h_closed
    simpa using h_closed.closure_eq
  · intro h_eq
    have h_subset : closure (interior (A : Set X)) ⊆ interior A := by
      simpa [h_eq]
    exact isClosed_of_closure_subset h_subset