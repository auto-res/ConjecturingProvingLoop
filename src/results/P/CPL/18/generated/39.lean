

theorem P1_closure_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure A ∩ interior A) := by
  -- The intersection coincides with `interior A`, since `interior A ⊆ closure A`.
  have h_eq : (closure (A : Set X) ∩ interior A : Set X) = interior A := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      have h_cl : x ∈ closure (A : Set X) :=
        subset_closure (interior_subset hx)
      exact And.intro h_cl hx
  -- Hence the statement follows from `P1` for `interior A`.
  simpa [h_eq] using (P1_interior (X := X) (A := A))

theorem P1_iterate {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h0 : Topology.P1 (A 0)) (hstep : ∀ n, Topology.P1 (A n) → Topology.P1 (A (n + 1))) : ∀ n, Topology.P1 (A n) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => exact hstep n ih

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : Topology.P3 B → Topology.P3 (((Set.univ : Set X).prod B)) := by
  intro hB
  have hUniv : Topology.P3 (Set.univ : Set X) := P3_univ (X := X)
  simpa using
    (P3_prod (X := X) (Y := Y) (A := (Set.univ : Set X)) (B := B) hUniv hB)