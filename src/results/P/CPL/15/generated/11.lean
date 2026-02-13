

theorem P1_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (hcl : IsClosed A) : P1 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    have hx' : x ∈ interior (closure A) := h3 hx
    simpa [hcl.closure_eq] using hx'
  exact subset_closure hx_int

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  intro x hx
  classical
  -- Since `X` is a subsingleton and `A` is non-empty, we have `A = univ`.
  have hAu : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; simp
    · intro _; 
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
  -- Hence `interior A = univ`.
  have hInt : interior A = (Set.univ : Set X) := by
    simpa [hAu, interior_univ]
  -- Therefore every point of `A` belongs to `closure (interior A)`.
  simpa [hInt, closure_univ] using (Set.mem_univ x)