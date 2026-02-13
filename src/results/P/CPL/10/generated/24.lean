

theorem P3_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P3 A ↔ Topology.P1 A := by
  -- First, obtain `P2 A` from the density assumption.
  have hP2 : Topology.P2 A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  -- From `P2 A` we can extract both `P1 A` and `P3 A`.
  have hP1 : Topology.P1 A :=
    ((Topology.P2_iff_P1_P3 (X := X) (A := A)).1 hP2).1
  have hP3 : Topology.P3 A :=
    ((Topology.P2_iff_P1_P3 (X := X) (A := A)).1 hP2).2
  exact ⟨fun _ => hP1, fun _ => hP3⟩

theorem P3_exists_dense {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Topology.P3 A ∧ Dense A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact P3_univ (X := X)
  · simpa using dense_univ

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` is in the closure of the interior of `A`
  have hx_cl : (x : X) ∈ closure (interior A) := hA hxA
  -- transport the membership through the homeomorphism
  have : (e x) ∈ closure (interior (e '' A)) := by
    -- first, regard it as a point in `e '' closure (interior A)`
    have h1 : (e x) ∈ e '' closure (interior A) := by
      exact ⟨x, hx_cl, rfl⟩
    -- rewrite using `image_closure`
    have h2 : (e x) ∈ closure (e '' interior A) := by
      simpa [e.image_closure (interior A)] using h1
    -- rewrite using `image_interior`
    simpa [e.image_interior A] using h2
  exact this

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P2 A) : Topology.P2 (e '' A) := by
  intro y hy
  -- Pick a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of the closure of the interior of `A`
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- Transport this membership through `e`
  have h₁ : (e x : Y) ∈ e '' interior (closure (interior A)) :=
    ⟨x, hx_int, rfl⟩
  -- Rewrite using `image_interior`
  have h₂ : (e x) ∈ interior (e '' closure (interior A)) := by
    simpa [e.image_interior (closure (interior A))] using h₁
  -- Rewrite using `image_closure`
  have h₃ : (e x) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (interior A)] using h₂
  -- Relate the two closures via `image_interior`
  have h_closure_eq :
      (closure (e '' interior A) : Set Y) = closure (interior (e '' A)) := by
    simpa using
      congrArg (closure : Set Y → Set Y) (e.image_interior A)
  -- Conclude by rewriting with the obtained equality
  simpa [h_closure_eq] using h₃

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} (hA : Topology.P3 A) : Topology.P3 (e '' A) := by
  intro y hy
  -- pick a preimage point `x`
  rcases hy with ⟨x, hxA, rfl⟩
  -- from `P3` we know `x ∈ interior (closure A)`
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- transport through `e`
  have h₁ : (e x : Y) ∈ e '' interior (closure A) := ⟨x, hx_int, rfl⟩
  -- rewrite using `image_interior`
  have h₂ : (e x) ∈ interior (e '' closure A) := by
    simpa [e.image_interior (closure A)] using h₁
  -- rewrite using `image_closure` and finish
  simpa [e.image_closure A] using h₂

theorem P1_iff_P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P1 A ↔ Topology.P1 (e '' A) := by
  constructor
  · intro hA
    exact P1_image_homeomorph (e := e) hA
  · intro hImg
    -- transport `P1` back through `e.symm`
    have h' : Topology.P1 ((e.symm) '' (e '' A)) :=
      P1_image_homeomorph (e := e.symm) (A := e '' A) hImg
    -- identify the image `e.symm '' (e '' A)` with `A`
    have hEq : ((e.symm) '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, by
          simp⟩
    simpa [hEq] using h'