# pipes

I made [free monad using church encoding](https://github.com/srhhma/lean-pipes/blob/main/Pipes/FreeMonad.lean) (though I couldnt make Proxy using it - couldnt make the function [`flipComposeResponse`](https://github.com/srhhma/lean-pipes/blob/f9fd768de2cd874cb459ed7a511aaddf1a69d15e/Pipes/InternalProxyF.lean#L113))

Also tried to make Church-encoded Proxy ([though couldnt make `connectProducerConsumer` too](https://github.com/srhhma/lean-pipes/blob/f9fd768de2cd874cb459ed7a511aaddf1a69d15e/Pipes/Internal.lean#L200C22-L200C45) and theorems that are present in [coq version](https://www.google.com/search?q=pipes+coq&oq=pipes+coq&gs_lcrp=EgZjaHJvbWUyBggAEEUYOTIICAEQABgWGB4yCAgCEAAYFhgeMg0IAxAAGIYDGIAEGIoFMgoIBBAAGIAEGKIEMgcIBRAAGO8FMgoIBhAAGIAEGKIEMgoIBxAAGIAEGKIEMgcICBAAGO8F0gEINjI1N2owajeoAgCwAgA&sourceid=chrome&ie=UTF-8))

### UPDATE
