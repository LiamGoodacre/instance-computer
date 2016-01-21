import Data.Vect
import Data.Fin

-- | Possible kinds of type
data RepKind
  = Arr RepKind RepKind
  | Star
  -- TODO: add Constraint, Row, etc

RepKinds : Nat -> Type
RepKinds n = Vect n RepKind

-- | Reference a variable in scope of a given `Kind`
data RepVar : Fin n -> (scope : RepKinds n) -> RepKind -> Type where
  Stop : RepVar FZ (k :: ks) k
  Pop  : RepVar i ks k -> RepVar (FS i) (o :: ks) k

-- | Representation of types
-- | TODO: environment
data RepType : (scope : RepKinds n) -> (kindOfType : RepKind) -> Type where
  -- | Type variable
  Var    : RepVar i ks k -> RepType ks k
  -- | Universal quantification
  Forall : RepType (k :: ks) Star -> RepType ks Star
  -- | Type application
  App    : RepType ks (Arr i o) -> RepType ks i -> RepType [] o
  -- | Function type
  Fun    : RepType ks Star -> RepType ks Star -> RepType ks Star

-- | Proper types have `Kind` `Star`
ProperType : RepKinds n -> Type
ProperType ks = RepType ks Star

namespace Filling
  -- | Sequence of types to fill in the arguments of a higher kinded type
  -- | TODO: environment
  data FilledKind : (typeVars : RepKinds n) -> (kind : RepKind) -> Type where
    Nil : FilledKind ts Star
    (::) : RepVar i ts d -> FilledKind ts c -> FilledKind ts (Arr d c)

  -- | Example: forall f a. Free f a
  filledKindExample : FilledKind [Arr Star Star, Star] (Arr (Arr Star Star) (Arr Star Star))
  filledKindExample = [Stop, Pop Stop]

-- | Representation of a data type's constructors
record RepCtor (dataKind : RepKind) where
  constructor MkCtor
  name      : String
  -- | All top level type variables
  typeVars  : RepKinds n
  -- | Constructor parameters with the `typeVars` and the data type in scope
  params    : List (ProperType (typeVars ++ [dataKind]))
  -- | Type arguments of the resulting data type
  finalTypeArgs : FilledKind typeVars kind

-- | Representation of data types
record RepData where
  constructor MkData
  -- The `Kind` of the data type, e.g. kind of `Maybe` is `Arr Star Star`
  kind  : RepKind
  -- All constructors for the data type
  ctors : List (RepCtor kind)

{-
  POSSIBLE CONSIDERATIONS
  want to guarantee that computed instances can
    only use type args - cannot inspect types of parameters
    specify constraints: generally, for particular type arguments of higher kinded types, etc
    fail deriving: data type not compatible, etc
-}
