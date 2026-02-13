

theorem P2_preimage_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} {f : X → Y} : Continuous f → IsOpen B → P2 (f ⁻¹' B) := by
  intro hf hB
  have hOpen : IsOpen (f ⁻¹' B) := hB.preimage hf
  exact P2_of_open (X := X) (A := f ⁻¹' B) hOpen

theorem P1_prod₃ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 (Set.prod A (Set.prod B C)) := by
  intro hP1A hP1B hP1C
  -- obtain `P1` for `B ×ˢ C`
  have hBC : P1 (Set.prod B C) :=
    P1_prod (X := Y) (Y := Z) (A := B) (B := C) hP1B hP1C
  -- combine with `A`
  have hABC : P1 (Set.prod A (Set.prod B C)) :=
    P1_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hP1A hBC
  exact hABC

theorem P2_prod₃ {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 (Set.prod A (Set.prod B C)) := by
  intro hP2A hP2B hP2C
  -- obtain `P2` for `B ×ˢ C`
  have hBC : P2 (Set.prod B C) :=
    P2_prod (X := Y) (Y := Z) (A := B) (B := C) hP2B hP2C
  -- combine with `A`
  have hABC : P2 (Set.prod A (Set.prod B C)) :=
    P2_prod (X := X) (Y := Y × Z) (A := A) (B := Set.prod B C) hP2A hBC
  exact hABC