

theorem P2_implies_P3 {A : Set X} : P2 A → P3 A := by
  intro hP2
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h1 : closure (interior A) ⊆ closure A := by
      have : (interior A : Set X) ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono h1
  exact Set.Subset.trans hP2 hsubset

theorem P1_union {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hPA hPB
  dsimp [P1] at hPA hPB ⊢
  intro x hx
  cases hx with
  | inl hA =>
      -- `x ∈ A`
      have hxA : x ∈ closure (interior A) := hPA hA
      -- `closure (interior A) ⊆ closure (interior (A ∪ B))`
      have hsubset : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) := by
        -- first, `interior A ⊆ interior (A ∪ B)`
        have hInt : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have hASub : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono hASub
        -- now take closures
        exact closure_mono hInt
      exact hsubset hxA
  | inr hB =>
      -- `x ∈ B`
      have hxB : x ∈ closure (interior B) := hPB hB
      -- `closure (interior B) ⊆ closure (interior (A ∪ B))`
      have hsubset : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) := by
        -- first, `interior B ⊆ interior (A ∪ B)`
        have hInt : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have hBSub : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono hBSub
        -- now take closures
        exact closure_mono hInt
      exact hsubset hxB

theorem P1_empty : P1 (∅ : Set X) := by
  dsimp [P1]
  exact Set.empty_subset _

theorem P2_univ : P2 (Set.univ : Set X) := by
  dsimp [P2]
  simpa

theorem exists_dense_subset_of_P1 {A : Set X} : P1 A → ∃ B : Set X, B ⊆ A ∧ closure B = closure A := by
  intro hP1
  refine ⟨interior A, interior_subset, ?_⟩
  apply Set.Subset.antisymm
  · exact closure_mono interior_subset
  ·
    have h : (A : Set X) ⊆ closure (interior A) := hP1
    have : closure A ⊆ closure (closure (interior A)) := closure_mono h
    simpa [closure_closure] using this

theorem P3_closed_implies_open {A : Set X} : IsClosed A → P3 A → IsOpen A := by
  intro hClosed hP3
  -- Since `A` is closed, `closure A = A`.
  have h_closure : closure A = (A : Set X) := IsClosed.closure_eq hClosed
  -- From `P3`, we obtain `A ⊆ interior A`.
  have h_subset : (A : Set X) ⊆ interior A := by
    have : (A : Set X) ⊆ interior (closure A) := hP3
    simpa [h_closure] using this
  -- Always, `interior A ⊆ A`.
  have h_subset' : interior A ⊆ A := interior_subset
  -- Hence, `interior A = A`.
  have h_eq : interior A = A := Set.Subset.antisymm h_subset' h_subset
  -- The interior is open, so `A` is open.
  have : IsOpen (interior A) := isOpen_interior
  simpa [h_eq] using this

theorem P1_subsingleton [Subsingleton X] {A : Set X} : P1 A := by
  classical
  dsimp [P1]
  intro x hx
  -- In a subsingleton type, any nonempty set is `univ`
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hx
  -- Now `closure (interior A)` is `univ`, so the goal is immediate
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hAuniv, interior_univ, closure_univ] using this