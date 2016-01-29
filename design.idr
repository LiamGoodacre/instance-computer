import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

%default total

namespace Kinding

  -- | Possible kinds of type
  data RepKind
    = Arr RepKind RepKind
    | Star
    -- TODO: add Constraint, Row, etc

  infixr 4 :=>
  (:=>) : RepKind -> RepKind -> RepKind
  (:=>) = Arr

  RepKinds : Nat -> Type
  RepKinds n = Vect n RepKind


namespace VariableReferencing

  -- | Reference a variable in scope of a given `Kind`
  data Item : Vect n t -> t -> Fin n -> Type where
    Stop : Item (k :: ks) k 0
    Pop  : Item ks k i -> Item (o :: ks) k (FS i)

  FromFin : (ks : RepKinds n) -> (i : Fin n) -> Item ks (Vect.index i ks) i
  FromFin (v :: vs) FZ     = Stop
  FromFin (v :: vs) (FS i) = Pop (FromFin vs i)


namespace Environments

  FnKind : RepKind
  FnKind = Star :=> Star :=> Star

  ArrKind : RepKind
  ArrKind = Star :=> Star

  DefaultEnv : Vect 2 RepKind
  DefaultEnv = [ FnKind
               , ArrKind
               ]

  FnType : Item DefaultEnv FnKind FZ
  FnType = FromFin DefaultEnv 0

  ArrayType : Item DefaultEnv (Star :=> Star) 1
  ArrayType = FromFin DefaultEnv 1


namespace Typing

  -- | Representation of types
  data RepType : (env : RepKinds e) ->
                 (scope : RepKinds n) ->
                 (kindOfType : RepKind) ->
                 Type where
    -- | Type variable
    Var : Item ks k i -> RepType es ks k
    -- | Universal quantification
    Forall : RepType es (ks ++ [k]) Star -> RepType es ks Star
    -- | Type application
    App : RepType es ks (i :=> o) -> RepType es ks i -> RepType es ks o
    -- | Function type - TODO: remove in favour of environment?
    Fun : RepType es ks Star -> RepType es ks Star -> RepType es ks Star
    -- | Reference types in the environment
    Other : Item es e i -> RepType es ks e

  extendTypeEnv : RepType es ks k -> RepType (e :: es) ks k
  extendTypeEnv (Var x) = Var x
  extendTypeEnv (Forall x) = Forall (extendTypeEnv x)
  extendTypeEnv (App x y) = App (extendTypeEnv x) (extendTypeEnv y)
  extendTypeEnv (Fun x y) = Fun (extendTypeEnv x) (extendTypeEnv y)
  extendTypeEnv (Other x) = Other (Pop x)

  -- | Proper types have `Kind` `Star`
  ProperType : RepKinds e -> RepKinds n -> Type
  ProperType es ks = RepType es ks Star

  var : (i : Fin n) -> RepType es ks (Vect.index i ks)
  var i {ks} = Var (FromFin ks i)

  infix 5 :$
  (:$) : RepType es ks (i :=> o) -> RepType es ks i -> RepType es ks o
  (:$) = App

  infixl 4 :->
  (:->) : ProperType es ks -> ProperType es ks -> ProperType es ks
  (:->) = Fun

  other : (i : Fin n) -> RepType es ks (Vect.index i es)
  other i {es} = Other (FromFin es i)


namespace Filling

  -- | Sequence of types to fill in the arguments of a higher kinded type
  data FilledKind : (env : RepKinds e) -> (typeVars : RepKinds n) -> (kind : RepKind) -> Type where
    Nil  : FilledKind es ts Star
    (::) : RepType es ts d -> FilledKind es ts c -> FilledKind es ts (d :=> c)

  extendFilledEnv : (e : RepKind) -> FilledKind es ks k -> FilledKind (e :: es) ks k
  extendFilledEnv e [] = []
  extendFilledEnv e (x :: y) = extendTypeEnv x :: extendFilledEnv e y

  filledType : FilledKind (with Vect (kind :: env)) vars kind ->
               ProperType (with Vect (kind :: env)) vars
  filledType xs = go (other 0) xs where
    go : RepType env vars kind -> FilledKind env vars kind -> ProperType env vars
    go m [] = m
    go m (x :: y) = go (m :$ x) y

  -- | Example: forall f a. Free f a
  filledKindExample : FilledKind [] [Star :=> Star, Star] ((Star :=> Star) :=> Star :=> Star)
  filledKindExample = [var 0, var 1]


namespace DataTyping

  -- | Representation of a data type's constructors
  record RepCtor (dataKind : RepKind) where
    constructor MkCtor
    name : String
    -- | Available types in the environment
    environment : RepKinds e
    -- | All top level type variables
    typeVars : RepKinds n
    -- | Constructor parameters with the `typeVars` and the data type in scope
    params : Vect paramCount (ProperType environment (dataKind :: typeVars))
    -- | Type arguments of the resulting data type
    finalTypeArgs : FilledKind environment (dataKind :: typeVars) dataKind

  -- | Representation of data types
  record RepData where
    constructor MkData
    -- The `Kind` of the data type, e.g. kind of `Maybe` is `Arr Star Star`
    kind : RepKind
    -- All constructors for the data type
    ctors : Vect sumCount (RepCtor kind)

  datatype : (kind : RepKind) -> Vect n (RepCtor kind) -> RepData
  datatype = MkData

  self : RepType es (k :: ks) k
  self = var 0


namespace Valuing

  -- rep was 3rd arg but https://github.com/idris-lang/Idris-dev/issues/1944
  data RepValue : ProperType env vars -> Type where
    MkValue : (rep : RepData) ->
              Item (ctors rep) ctor i ->
              (env : RepKinds e) ->
              (vars : RepKinds v) ->
              (args : All RepValue (params ctor)) ->
              (finalArgs : FilledKind env vars (kind rep)) ->
              RepValue (filledType (extendFilledEnv (kind rep) finalArgs))


namespace DataExamples

  -- Unit : * where
  --   Unit : Unit
  Unit : RepData
  Unit = datatype Star
    [ MkCtor "unit" [] [] [] []
    ]

  -- unit : Unit
  unit : RepValue (the (RepType [Star] [] Star) (other 0))
  unit = MkValue Unit Stop [] [] [] []

  -- Bool : * where
  --   True : Bool
  --   False : Bool
  Bool : RepData
  Bool = datatype Star
    [ MkCtor "true"  [] [] [] []
    , MkCtor "false" [] [] [] []
    ]

  true : RepValue (the (RepType [Star] [] Star) (other 0))
  true = MkValue Bool Stop [] [] [] []

  -- Maybe : * -> * where
  --   Nothing : forall (t : *). Maybe t
  --   Just    : forall (t : *). t -> Maybe t
  maybe : RepData
  maybe = datatype (Star :=> Star)
    [ MkCtor "nothing" [] [Star] []      [var 1]
    , MkCtor "just"    [] [Star] [var 1] [var 1]
    ]

  -- Either : * -> * -> * where
  --   Left  : forall (l, r : *). l -> Either l r
  --   Right : forall (l, r : *). r -> Either l r
  either : RepData
  either = datatype (Star :=> Star :=> Star)
    [ MkCtor "left"  [] [Star, Star] [var 1] [var 1, var 2]
    , MkCtor "right" [] [Star, Star] [var 2] [var 1, var 2]
    ]

  -- Pair : * -> * -> * where
  --   Pair : forall (l, r : *). l -> r -> Pair l r
  pair : RepData
  pair = datatype (Star :=> Star :=> Star)
    [ MkCtor "pair" [] [Star, Star] [var 1, var 2] [var 1, var 2]
    ]

  -- List : * -> * where
  --   Nil  : forall (t : *). List t
  --   Cons : forall (t : *). t -> List t -> List t
  list : RepData
  list = datatype (Star :=> Star)
    [ MkCtor "nil"  [] [Star] [] [var 1]
    , MkCtor "cons" [] [Star] [var 1, self :$ var 1] [var 1]
    ]

  -- Coyoneda : (* -> *) -> * -> * where
  --   Coyo : forall (f : * -> *) (a, b : *). (b -> a) -> (f b) -> Coyoneda f a
  coyoneda : RepData
  coyoneda = datatype ((Star :=> Star) :=> Star :=> Star)
    [ MkCtor "coyo" [] [Star :=> Star, Star, Star]
                       [var 3 :-> var 2, var 1 :$ var 2]
                       [var 1, var 2]
    ]

  -- Free : (* -> *) -> * -> * where
  --   Pure : forall (f : * -> *) (a : *). a -> Free f a
  --   Next : forall (f : * -> *) (a : *). f (Free f a) -> Free f a
  free : RepData
  free = datatype ((Star :=> Star) :=> Star :=> Star)
    [ MkCtor "pure" [] [Star :=> Star, Star] [var 2] [var 1, var 2]
    , MkCtor "next" [] [Star :=> Star, Star]
                       [var 1 :$ ((self :$ var 1) :$ var 2)]
                       [var 1, var 2]
    ]

  -- Exists : (* -> *) -> * where
  --   MkExists : forall (p : * -> *). (forall r. (forall i. p i -> r) -> r) -> Exists p
  exists : RepData
  exists = datatype ((Star :=> Star) :=> Star)
    [ MkCtor "mkExists" [] [Star :=> Star]
                           [Forall (Forall ((var 1 :$ var 3) :-> var 2) :-> var 2)]
                           [var 1]
    ]


  -- | Here we have a reference to `String : *`
  -- FullName : * where
  --   MkFullName : String -> String -> FullName
  fullName : RepData
  fullName = datatype Star
    [ MkCtor "mkFullName" [Star] [] [other 0, other 0] []
    ]


  {-
    POSSIBLE CONSIDERATIONS
    want to guarantee that computed instances can
      only use type args - cannot inspect types of parameters
      specify constraints: generally, for particular type arguments of higher kinded types, etc
      fail deriving: data type not compatible, etc
  -}

