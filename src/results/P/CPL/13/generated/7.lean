

theorem P3_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} : interior (closure A) = Set.univ → Topology.P3 A := by
  intro h
  dsimp [Topology.P3] at *
  intro x hx
  simpa [h] using (Set.mem_univ x)

theorem P1_unionᵢ {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, interior (A i)) := by
  -- Build P1 for each interior set (mentioning `h` so it's not unused)
  have h' : ∀ i, Topology.P1 (interior (A i)) := by
    intro i
    have _ := h i
    simpa using (Topology.P1_interior (A := A i))
  simpa using
    (P1_iUnion (ι := ι) (X := X) (A := fun i => interior (A i)) h')

theorem P2_sUnion_of_open {X : Type*} [TopologicalSpace X] {𝒜 : Set (Set X)} (h₁ : ∀ A ∈ 𝒜, IsOpen A) : Topology.P2 (⋃₀ 𝒜) := by
  dsimp [Topology.P2]
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hA_mem, hxA⟩
  have hP2A : Topology.P2 A := Topology.P2_of_open (A := A) (h₁ A hA_mem)
  have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
  have h_subset : interior (closure (interior A)) ⊆
                  interior (closure (interior (⋃₀ 𝒜))) := by
    have h1 : interior A ⊆ interior (⋃₀ 𝒜) := by
      apply interior_mono
      intro y hy
      exact Set.mem_sUnion.2 ⟨A, hA_mem, hy⟩
    have h2 : closure (interior A) ⊆ closure (interior (⋃₀ 𝒜)) :=
      closure_mono h1
    exact interior_mono h2
  exact h_subset hx_in

theorem P3_closure_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  exact Set.Subset.trans subset_closure h

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {A : Set X} (hA : Topology.P1 A) : Topology.P1 (e '' A) := by
  dsimp [Topology.P1] at *
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx : x ∈ closure (interior A) := hA hxA
  -- `e` maps this point into the image of that closure
  have hx_img : (e x : Y) ∈ e '' closure (interior A) := ⟨x, hx, rfl⟩
  -- Identify the image of the closure and of the interior through `e`
  have h_closure_eq := e.image_closure (s := interior A)
  have h_interior_eq := e.image_interior (s := A)
  -- Transport membership through these equalities
  have hx_img' : (e x : Y) ∈ closure (e '' interior A) := by
    simpa [h_closure_eq] using hx_img
  have : (e x : Y) ∈ closure (interior (e '' A)) := by
    simpa [h_interior_eq] using hx_img'
  exact this

theorem P3_countable_union {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h : ∀ n, Topology.P3 (A n)) : Topology.P3 (⋃ n, A n) := by
  dsimp [Topology.P3] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨n, hxAn⟩
  have hP3n : Topology.P3 (A n) := h n
  have hx_in : x ∈ interior (closure (A n)) := hP3n hxAn
  have h_subset : interior (closure (A n)) ⊆ interior (closure (⋃ m, A m)) := by
    apply interior_mono
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨n, hy⟩
  exact h_subset hx_in