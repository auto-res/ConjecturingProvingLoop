

theorem Topology.P1_prod3 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : Topology.P1 A → Topology.P1 B → Topology.P1 C → Topology.P1 (((A ×ˢ B) ×ˢ C) : Set ((X × Y) × Z)) := by
  intro hP1A hP1B hP1C
  -- First, obtain `P1` for `A ×ˢ B`.
  have hP1AB : Topology.P1 (A ×ˢ B) :=
    (P1_prod (A := A) (B := B) (X := X) (Y := Y) hP1A hP1B)
  -- Then combine with `C` to get the desired result.
  simpa using
    (P1_prod (A := (A ×ˢ B)) (B := C) (X := X × Y) (Y := Z) hP1AB hP1C)

theorem Topology.P2_prod3 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (((A ×ˢ B) ×ˢ C) : Set ((X × Y) × Z)) := by
  intro hP2A hP2B hP2C
  -- First, obtain `P2` for `A ×ˢ B`.
  have hP2AB : Topology.P2 (A ×ˢ B) :=
    P2_prod (A := A) (B := B) (X := X) (Y := Y) hP2A hP2B
  -- Then combine with `C`.
  simpa using
    (P2_prod (A := (A ×ˢ B)) (B := C) (X := X × Y) (Y := Z) hP2AB hP2C)

theorem Topology.P3_prod3 {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : Topology.P3 A → Topology.P3 B → Topology.P3 C → Topology.P3 (((A ×ˢ B) ×ˢ C) : Set ((X × Y) × Z)) := by
  intro hP3A hP3B hP3C
  -- First, obtain `P3` for `A ×ˢ B`.
  have hP3AB : Topology.P3 (A ×ˢ B) :=
    P3_prod (A := A) (B := B) (X := X) (Y := Y) hP3A hP3B
  -- Then combine with `C`.
  simpa using
    (P3_prod (A := (A ×ˢ B)) (B := C) (X := X × Y) (Y := Z) hP3AB hP3C)