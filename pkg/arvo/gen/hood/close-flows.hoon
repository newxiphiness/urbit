::  Deletes all stale ames flows from failed (re) subscriptions
::
::    It runs in dry mode by default, printing the flows that can be closed.
::    To actually close the flows, run with |close-flows, =dry |
::
::    verbosity:
::      |close-flows, =veb %1  ::  flows already in closing
::      |close-flows, =veb %2  ::  stale (re) subscriptions
::      |close-flows, =veb %3  ::  stale current subscription
::      |close-flows, =veb %4  ::  latest subscription was %nacked
::
/=  gall-raw  /sys/vane/gall
::
:-  %say
|=  $:  [now=@da eny=@uvJ bec=beak]
        arg=~
        peer=(unit @p)
        dry=?
        veb=?(%1 %2 %3 %4)
    ==
::
=/  our-gall  (gall-raw p.bec)
=/  peers-map
  .^((map ship ?(%alien %known)) %ax /(scot %p p.bec)//(scot %da now)/peers)
=/  gall-yokes
  .^((map dude:gall yoke:our-gall) %gy /(scot %p p.bec)//(scot %da now)/$)
::
=/  peers=(list ship)
  %+  murn  ~(tap by peers-map)
  |=  [=ship val=?(%alien %known)]
  ?:  =(ship p.bec)
    ~  ::  this is weird, but we saw it
  ?-  val
    %alien  ~
    %known  (some ship)
  ==
::
=;  bones=(list [ship bone])
  :-  %helm-ames-kroc
  ~?  dry  "#{<(lent bones)>} flows can be closed"
  dry^bones
::
%+  roll  peers
|=  [=ship bones=(list [ship bone])]
?:  &(?=(^ peer) !=(u.peer ship))
  bones
::
=+  .^  =ship-state:ames
        %ax  /(scot %p p.bec)//(scot %da now)/peers/(scot %p ship)
    ==
=/  =peer-state:ames  ?>(?=(%known -.ship-state) +.ship-state)
|^
::
%+  roll  ~(tap by resubscriptions)
|=  [[=wire flows=(list [bone sub-nonce=@ last-nonce=(unit @ud)])] bones=_bones]
::
%-  flop  %-  tail
%+  roll  (sort flows |=([[@ n=@ *] [@ m=@ *]] (lte n m)))
|=  [[=bone nonce=@ app-nonce=(unit @ud)] resubs=_(lent flows) bones=_bones]
::
=/  app=term  ?>(?=([%gall %use sub=@ *] wire) i.t.t.wire)
=/  =path     (slag 7 wire)
=/  log=tape
  "[bone={<bone>} agent={<app>} nonces={<[wire=nonce app=app-nonce]>}] {<path>}"
=;  corkable=?
  =?  bones  corkable  [[ship bone] bones]
  (dec resubs)^bones
::  checks if this is a stale re-subscription
::
?.  =(resubs 1)
  ::  if there are more than one subscription per wire, we assert that this is
  ::  indeed a (post-nonce) resubscription -- we have retrieved a sub-nonce
  ::  from the agent -- and the nonce in the flow is less than the latest one
  ::
  ?>  &(?=([~ @] app-nonce) (lth nonce u.app-nonce))
  ~?  ?=(%2 veb)  [ship (weld "stale %watch plea " log)]
  &
::  if there's only one subscription (or this is the latest one, since we sort
::  flows by nonce) we consider it stale if the nonce in the wire is less than
::  the latest subscription the agent knows about, since that should have been
::  removed from %gall, and we don't need to coordindate between %ames and %gall
::
?:  ?&  ?=([~ @] app-nonce)
        (lth nonce u.app-nonce)
    ==
  ~?  ?=(%3 veb)  [ship (weld "latest subscription flow is not live " log)]
  &
::  if we couldn't retrieve the nonce for the latest flow, we could be dealing
::  with a %poke (that doesn't touch boat/boar.yoke) or with an %ames/%gall
::  desync where %gall deleted the subscription but %ames didn't. since we can't
::  know for sure (we would need to know inspect the agent responsible) we mark
::  it as non-corkable
::
?~  app-nonce  |
::  if there's a nonce this is the current subscription and can be safely corked
::  if there is a flow with a naxplanation ack on a backward bone
::
=+  backward-bone=(mix 0b10 bone)
?.  =(%2 (mod backward-bone 4))
  |
?~  (~(get by rcv.peer-state) backward-bone)
  |
~?  ?=(%4 veb)  [ship (weld "%watch plea was %nacked " log)]
&
::
++  resubscriptions
  %+  roll  ~(tap by snd.peer-state)
  |=  $:  [=forward=bone message-pump-state:ames]
          subs=(jar path [bone sub-nonce=@ud last-nonce=(unit @ud)])
      ==
  ?~  duct=(~(get by by-bone.ossuary.peer-state) forward-bone)
    subs
  ?.  ?=([* [%gall %use sub=@ @ %out ship=@ app=@ *] *] u.duct)
    subs
  =/  =wire           i.t.u.duct
  =/  nonce=(unit @)  ?~((slag 7 wire) ~ (slaw %ud &8.wire))
  =*  ship            &6.wire
  =*  agent           &7.wire
  =/  path            ?~(nonce |7.wire |8.wire)
  =+  key=[path `@p`(slav %p ship) agent]
  ?~  yoke=(~(get by gall-yokes) agent)
    ~
  ?.  &(?=(%live -.u.yoke) (~(has by boat.u.yoke) key))
    ::  %pokes don't have an entry in boat.yoke, so we skip them
    ::
    subs
  =/  agent-nonce=(unit @ud)  (~(get by boar.u.yoke) key)
  ::
  ?:  (~(has in closing.peer-state) forward-bone)
    ~?  ?=(%1 veb)
      :-  ship
      %+  weld  "bone={<forward-bone>} in closing, "
      "#{<~(wyt in live:packet-pump-state)>} packets retrying -- {<key>}"
    subs
  %-  ~(add ja subs)
  ::  0 for old pre-nonce subscriptions (see watches-8-to-9:load in %gall)
  ::
  :_  [forward-bone ?~(nonce 0 u.nonce) agent-nonce]
  ?~  nonce  wire
  ::  don't include the sub-nonce in the key
  ::
  (weld (scag 7 wire) (slag 8 wire))
--
