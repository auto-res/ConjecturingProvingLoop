

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B)) : Topology.P1 (A := Set.prod A B) := by
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P1` on the two coordinates
  have hx : p.fst ∈ closure (interior A) := hA hpA
  have hy : p.snd ∈ closure (interior B) := hB hpB
  -- Combine the information in the product space
  have h_prod_mem : p ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    ⟨hx, hy⟩
  -- Relate the product of closures with the closure of the product
  have h_prod_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using closure_prod_eq
  have hp_closure_int : p ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_prod_eq] using h_prod_mem
  -- `interior A × interior B ⊆ interior (A × B)`
  have h_int_subset :
      Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
    have h_sub : Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
      intro q hq
      exact ⟨interior_subset hq.1, interior_subset hq.2⟩
    have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
      (isOpen_interior.prod isOpen_interior)
    exact interior_maximal h_sub h_open
  -- Taking closures preserves inclusion
  have h_closure_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_int_subset
  -- Conclude
  exact h_closure_subset hp_closure_int

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 (A := A) := by
  intro x hx
  classical
  -- Since `X` is a subsingleton, a non-empty set must be `univ`.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      -- All points are equal, hence `y ∈ A`.
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hx
  -- Rewrite the goal using `hA_univ`.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hA_univ, interior_univ, closure_univ] using this