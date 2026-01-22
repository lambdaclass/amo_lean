import Lake
open Lake DSL

package «amo-lean-toy» where
  -- Configuración del paquete
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,  -- Usar λ en lugar de fun
    ⟨`autoImplicit, false⟩    -- Desactivar implicits automáticos
  ]

@[default_target]
lean_lib «AmoLean» where
  -- Raíz de la biblioteca
  roots := #[`AmoLean]
  -- Archivos a compilar
  globs := #[
    .one `AmoLean,
    .submodules `AmoLean
  ]

-- Para futuro: dependencia de Mathlib
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4.git"
