

theorem P1_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P1 A) : closure (interior (closure A)) = closure A := by
  -- First, `closure A` satisfies `P1`.
  have hP1_closure : Topology.P1 (closure A) :=
    Topology.P1_closure (A := A) h
  -- Apply the equality given by `P1` to `closure A`.
  have h_eq : closure (interior (closure A)) = closure (closure A) :=
    Topology.closure_eq_of_P1 (A := closure A) hP1_closure
  -- `closure (closure A)` simplifies to `closure A`.
  simpa [closure_closure] using h_eq

theorem P3_open_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : (Topology.P3 A ↔ interior A = A) := by
  have h_eq : interior A = A := hA.interior_eq
  exact
    ⟨fun _ => h_eq, fun _ => Topology.P3_of_open (A := A) hA⟩

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h2 : closure A = Set.univ) : Topology.P2 A := by
  -- Unfold the definitions of `P1` and `P2`
  dsimp [Topology.P1, Topology.P2] at *
  intro x hxA
  -- From `P1`, we have `A ⊆ closure (interior A)`, hence
  -- `closure A ⊆ closure (interior A)`.
  have h_closure_sub : (closure A : Set X) ⊆ closure (interior A) := by
    have hA_subset : (A : Set X) ⊆ closure (interior A) := h1
    have h := closure_mono hA_subset
    simpa [closure_closure] using h
  -- Using `closure A = univ`, deduce `closure (interior A) = univ`.
  have h_univ : (closure (interior A) : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · intro y hy; exact Set.mem_univ y
    · have : (Set.univ : Set X) ⊆ closure (interior A) := by
        simpa [h2] using h_closure_sub
      exact this
  -- Therefore every point of `A` (in particular `x`) lies in the desired interior.
  have : x ∈ interior (closure (interior A)) := by
    have hx_univ : x ∈ (Set.univ : Set X) := Set.mem_univ x
    simpa [h_univ, interior_univ] using hx_univ
  exact this