

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact subset_trans hP2 interior_subset

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  have h : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono (subset_closure : interior A ⊆ closure (interior A))
  simpa [interior_interior] using h

theorem open_implies_P1_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ∧ P2 A := by
  -- The interior of an open set is the set itself
  have h_int : interior A = A := hA.interior_eq
  -- P1 : A ⊆ closure (interior A)
  have hP1 : P1 A := by
    dsimp [P1]
    simpa [h_int] using (subset_closure : A ⊆ closure A)
  -- P2 : A ⊆ interior (closure (interior A))
  have hP2 : P2 A := by
    dsimp [P2]
    simpa [h_int] using
      (interior_mono (subset_closure : A ⊆ closure A))
  exact And.intro hP1 hP2

theorem closed_and_P1_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (hP : P1 A) : A = closure (interior A) := by
  apply subset_antisymm
  · simpa using hP
  ·
    have h : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [hA.closure_eq] using h

theorem dense_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : closure A = closure (interior A) := by
  apply subset_antisymm
  ·
    -- First inclusion: `closure A ⊆ closure (interior A)`
    have hA : (A : Set X) ⊆ closure (interior A) := by
      have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      exact subset_trans h h₁
    have : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using this
  ·
    -- Second inclusion: `closure (interior A) ⊆ closure A`
    have hIA : (interior A : Set X) ⊆ A := interior_subset
    simpa using closure_mono hIA

theorem P2_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : A ⊆ interior (closure A) := by
  exact
    subset_trans h
      (interior_mono
        (closure_mono (interior_subset : (interior A : Set X) ⊆ A)))

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  -- Unfold the definition of `P2`
  dsimp [P2] at *
  ----------------------------------------------------------------
  -- First, show `A ⊆ interior (closure (interior (A ∪ B)))`
  ----------------------------------------------------------------
  have hA' : (A : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    -- `interior A ⊆ interior (A ∪ B)`
    have h_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
      have h_sub : (A : Set X) ⊆ A ∪ B := by
        intro x hx
        exact Or.inl hx
      exact interior_mono h_sub
    -- Hence `closure (interior A) ⊆ closure (interior (A ∪ B))`
    have h_cl : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
      closure_mono h_int
    -- And so `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`
    have h_in : interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) :=
      interior_mono h_cl
    -- Chain with the hypothesis `hA`
    exact subset_trans hA h_in
  ----------------------------------------------------------------
  -- Next, show `B ⊆ interior (closure (interior (A ∪ B)))`
  ----------------------------------------------------------------
  have hB' : (B : Set X) ⊆ interior (closure (interior (A ∪ B))) := by
    -- `interior B ⊆ interior (A ∪ B)`
    have h_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
      have h_sub : (B : Set X) ⊆ A ∪ B := by
        intro x hx
        exact Or.inr hx
      exact interior_mono h_sub
    -- Hence `closure (interior B) ⊆ closure (interior (A ∪ B))`
    have h_cl : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
      closure_mono h_int
    -- And so `interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B)))`
    have h_in : interior (closure (interior B)) ⊆
        interior (closure (interior (A ∪ B))) :=
      interior_mono h_cl
    -- Chain with the hypothesis `hB`
    exact subset_trans hB h_in
  ----------------------------------------------------------------
  -- Finally, combine the two inclusions to obtain the goal
  ----------------------------------------------------------------
  intro x hx
  cases hx with
  | inl hxA => exact hA' hxA
  | inr hxB => exact hB' hxB