module Core.Quantity where

-- semiring
import Data.Semiring


data Quantity where
  Zero :: Quantity
  One  :: Quantity
  Inf  :: Quantity
  deriving (Eq, Ord, Show)

plusQ :: Quantity -> Quantity -> Quantity
plusQ Zero q    = q
plusQ q    Zero = q
plusQ One  One  = Inf
plusQ Inf  _    = Inf
plusQ _    Inf  = Inf

multQ :: Quantity -> Quantity -> Quantity
multQ Zero _    = Zero
multQ _    Zero = Zero
multQ One  q    = q
multQ q    One  = q
multQ Inf  _    = Inf


instance Semiring Quantity where
  zero  = Zero
  one   = One
  plus  = plusQ
  times = multQ

  fromNatural 0 = Zero
  fromNatural 1 = One
  fromNatural _ = Inf
  
