{-
  mios-bot:
    main:                mios-bot.hs
    source-dirs:         app
    when:
      - condition:       flag(bot)
        then:
          buildable:     true
        else:
          buildable:     false
    dependencies:
      - mios
      - gitrev
      - discord-hs
      - text==1.2.*
      - req
-}{
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

import qualified SAT.Mios as Mios
import Development.GitRev
import DiscordSecret (token)
{-
-- please make 'DiscordSecret.hs' here as:
> module DiscordSecret (token) where
> token :: String
> token = "a token got from the discordapp.com/developers/your bots web page"
-}

gitId :: String
gitId = "0.1 + https://github.com/shnarazk/mios/commit/" ++ $(gitHash)

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
    | any (T.isPrefixOf "p cnf ") $ take 10 (T.lines c) = do
        v <- ("-- " ++) <$> version
        result <- liftIO $ Mios.showAnswerFromString (T.unpack . T.unlines . tail . init . T.lines $ c)
        let res = "<@" ++ show uid ++ ">, I did. " ++ v ++ "\n```\n" ++ result ++ "```"
        void $ doFetch $ CreateMessage ch (T.pack res) Nothing
    | otherwise = return ()

type TypeCheckApp = (MessageCreateEvent :<>: MessageUpdateEvent) :> MnemonicHandler

instance EventHandler TypeCheckApp IO

main :: IO ()
main = runBot (Proxy :: Proxy (IO TypeCheckApp))
