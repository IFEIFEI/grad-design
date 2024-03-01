module Classes where
import Control.Monad

newtype Parser a = Parser {parse:: String -> [(a, String)]}

instance Functor Parser where
    fmap f p = Parser $ \inp -> fmap (\(a,cs)-> (f a, cs)) $ (parse p) inp

instance Applicative Parser where
    pure a = Parser $ \inp -> [(a,inp)]
    f <*> p= ap f p

instance Monad Parser where
    return a = Parser $ \inp -> [(a,inp)]
    p >>= f = Parser $ \inp -> concat [parse (f a) cs | (a, cs) <- parse p inp]

{- make the sequence parse to be a monid -}
class Monad m => MonadZero m where
    zero :: m a

class MonadZero m => MonadPlus m where
    (+-+) :: m a -> m a -> m a
