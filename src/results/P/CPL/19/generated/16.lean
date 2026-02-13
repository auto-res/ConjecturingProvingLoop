

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hp
  rcases hp with ⟨hpA, hpB⟩
  -- Apply `P1` to each coordinate.
  have hA : p.1 ∈ closure (interior A) := hP1A hpA
  have hB : p.2 ∈ closure (interior B) := hP1B hpB
  ------------------------------------------------------------------
  -- `p` lies in the product of the two closures.
  ------------------------------------------------------------------
  have h_prod : p ∈ (closure (interior A)) ×ˢ (closure (interior B)) :=
    ⟨hA, hB⟩
  -- Identify this product with a closure of a product.
  have h_cl_eq :
      closure ((interior A) ×ˢ (interior B)) =
        (closure (interior A)) ×ˢ (closure (interior B)) := by
    simpa using closure_prod_eq
  have h_cl_prod :
      p ∈ closure ((interior A) ×ˢ (interior B)) := by
    simpa [h_cl_eq] using h_prod
  ------------------------------------------------------------------
  -- The product of interiors is contained in the interior of the product.
  ------------------------------------------------------------------
  have h_subset_int :
      ((interior A) ×ˢ (interior B)) ⊆ interior (Set.prod A B) := by
    apply interior_maximal
    · intro q hq
      rcases hq with ⟨hq1, hq2⟩
      exact ⟨interior_subset hq1, interior_subset hq2⟩
    · exact (isOpen_interior.prod isOpen_interior)
  -- Taking closures preserves inclusions.
  have h_closure_subset :
      closure ((interior A) ×ˢ (interior B)) ⊆
        closure (interior (Set.prod A B)) :=
    closure_mono h_subset_int
  ------------------------------------------------------------------
  -- Conclude.
  ------------------------------------------------------------------
  exact h_closure_subset h_cl_prod

theorem P1_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} {f : X → Y} : Continuous f → IsOpen B → P1 (f ⁻¹' B) := by
  intro hf hB
  -- The preimage is open since `f` is continuous and `B` is open.
  have hOpen : IsOpen (f ⁻¹' B) := hB.preimage hf
  -- Open sets satisfy `P3`.
  have hP3 : P3 (f ⁻¹' B) :=
    P3_of_open (X := X) (A := f ⁻¹' B) hOpen
  -- For open sets, `P1` is equivalent to `P3`.
  exact ((P1_iff_P3_of_open (X := X) (A := f ⁻¹' B) hOpen).2) hP3

theorem P3_prod₃ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 (Set.prod A (Set.prod B C)) := by
  intro hP3A hP3B hP3C
  have hBC : P3 (Set.prod B C) :=
    P3_prod (A := B) (B := C) hP3B hP3C
  have hABC : P3 (Set.prod A (Set.prod B C)) :=
    P3_prod (A := A) (B := Set.prod B C) hP3A hBC
  exact hABC