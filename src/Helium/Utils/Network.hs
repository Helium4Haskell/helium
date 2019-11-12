module Helium.Utils.Network where


import qualified Network.Socket                as N
import           System.IO                      ( IOMode(..)
                                                , Handle
                                                )

connectTo :: N.HostName -> N.PortNumber -> IO Handle
connectTo host port = do
    addr : _ <- N.getAddrInfo Nothing (Just host) (Just (show port))
    sock     <- N.socket (N.addrFamily addr)
                         (N.addrSocketType addr)
                         (N.addrProtocol addr)
    N.connect sock (N.addrAddress addr)
    N.socketToHandle sock ReadWriteMode
