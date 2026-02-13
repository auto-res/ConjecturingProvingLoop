

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  -- Unfold the definition of `P1`
  unfold Topology.P1
  intro x hx
  classical
  -- First, show that `A` must be the whole space `Set.univ`
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewriting with `A = Set.univ`, everything becomes immediate
  simpa [hA_univ, isOpen_univ.interior_eq, closure_univ] using (Set.mem_univ x)

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A := by
  intro x hx
  classical
  -- `A` is nonempty (since `x ∈ A`) and the space is a subsingleton,
  -- hence `A = univ`.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using `hA_univ`; it reduces to `x ∈ univ`, solved by `simp`.
  simpa [hA_univ, closure_univ, isOpen_univ.interior_eq] using (by
    simp : x ∈ (Set.univ : Set X))

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A := by
  -- Unfold the definition of `P3`
  unfold Topology.P3
  intro x hx
  classical
  -- In a subsingleton space any nonempty set is the whole space
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewriting with `A = univ`, the goal becomes trivial
  simpa [hA_univ, closure_univ, isOpen_univ.interior_eq] using (Set.mem_univ x)