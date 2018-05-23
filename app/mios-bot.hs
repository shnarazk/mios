{-# LANGUAGE
    DataKinds
  , FlexibleInstances
  , MultiParamTypeClasses
  , OverloadedStrings
  , TemplateHaskell
  , TypeFamilies
  , TypeOperators
#-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Control.Monad
import Control.Monad.IO.Class
import Data.Proxy
import qualified Data.Text as T
import GHC.TypeLits
import Network.Discord

import SAT.Mios
import Development.GitRev
import DiscordSecret (token)

gitId :: String
gitId = versionId ++ "/commit/" ++ $(gitHash)

instance DiscordAuth IO where
  auth    = return $ Bot token
  version = return $ gitId
  runIO   = id

data MnemonicHandler

instance EventMap MnemonicHandler (DiscordApp IO) where
  type Domain   MnemonicHandler = Message
  type Codomain MnemonicHandler = ()

  mapEvent p (m@Message{ messageContent = c
                       , messageChannel = ch
                       , messageAuthor = User{userIsBot = bot, userId = uid}}
             )
    | bot = return ()
    | "```cnf" `T.isPrefixOf` c = do
        v <- ("-- version: " ++) <$> version
        let code = drop 6 (T.unpack c)
            res = "<@" ++ show uid ++ ">, I did. " ++ v ++ "\n```\n" ++ "satisfiability checking" ++ "```"
        void $ doFetch $ CreateMessage ch (T.pack res) Nothing
    | otherwise = return ()

type TypeCheckApp = (MessageCreateEvent :<>: MessageUpdateEvent) :> MnemonicHandler

instance EventHandler TypeCheckApp IO

main :: IO ()
main = runBot (Proxy :: Proxy (IO TypeCheckApp))
