

theorem P1_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : Topology.P1 B → Topology.P1 ((Set.univ : Set X) ×ˢ B) := by
  intro hP1B
  have hP1_univ : P1 (Set.univ : Set X) := by
    simpa using (P1_univ (X := X))
  simpa using
    (P1_prod (A := (Set.univ : Set X)) (B := B) hP1_univ hP1B)

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P2 A → Topology.P2 (e '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- Apply `P2` to obtain a point in the required interior.
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Transport this fact through the homeomorphism `e`.
  have h1 : (e x : Y) ∈ interior (e '' closure (interior A)) := by
    have : (e x : Y) ∈ (e '' interior (closure (interior A))) := ⟨x, hx, rfl⟩
    simpa [e.image_interior (closure (interior A))] using this
  -- Rewrite the set using the fact that `e` sends closures to closures.
  have h2 : (e x : Y) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (interior A)] using h1
  -- Rewrite once more using the fact that `e` sends interiors to interiors.
  have h3 : (e x : Y) ∈ interior (closure (interior (e '' A))) := by
    simpa [e.image_interior A] using h2
  exact h3

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} : Topology.P3 A → Topology.P3 (e '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `hP3` gives the required interior point on `X`.
  have hx : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Transport through the homeomorphism.
  have h1 : (e x : Y) ∈ interior (e '' closure (A : Set X)) := by
    have : (e x : Y) ∈ (e '' interior (closure (A : Set X))) := ⟨x, hx, rfl⟩
    simpa [e.image_interior (closure (A : Set X))] using this
  -- Rewrite using the fact that `e` sends closures to closures.
  simpa [e.image_closure (A : Set X)] using h1