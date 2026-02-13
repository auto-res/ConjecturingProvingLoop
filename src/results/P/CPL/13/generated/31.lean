

theorem P3_compl_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 (Aᶜ) := by
  simpa using (Topology.P3_of_open (A := Aᶜ) hA.isOpen_compl)

theorem P3_iff_P1_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (closure A)) : Topology.P3 A ↔ Topology.P1 (closure A) := by
  -- The closure of `A` is open by assumption, hence its interior is itself.
  have h_int_eq : interior (closure A) = closure A := hA.interior_eq
  -- Consequently, `closure (interior (closure A)) = closure A`.
  have h_cl_eq : closure (interior (closure A)) = closure A := by
    simpa [h_int_eq, closure_closure]
  -- `P1 (closure A)` holds unconditionally under these equalities.
  have hP1_closure : Topology.P1 (closure A) := by
    dsimp [Topology.P1]
    intro x hx
    simpa [h_cl_eq] using hx
  -- Likewise, `P3 A` always holds because `A ⊆ closure A = interior (closure A)`.
  have hP3A : Topology.P3 A := by
    dsimp [Topology.P3]
    intro x hx
    have hx_cl : x ∈ closure A := subset_closure hx
    simpa [h_int_eq] using hx_cl
  exact ⟨fun _ => hP1_closure, fun _ => hP3A⟩

theorem P1_prod_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (Set.prod (interior A) (interior B)) := by
  -- We first note that the interiors of `A` and `B` satisfy `P1`.
  have hA_int : Topology.P1 (interior A) := by
    simpa using (Topology.P1_interior (A := A))
  have hB_int : Topology.P1 (interior B) := by
    simpa using (Topology.P1_interior (A := B))
  -- Apply the product theorem for `P1`.
  simpa using
    (Topology.P1_prod (A := interior A) (B := interior B) hA_int hB_int)