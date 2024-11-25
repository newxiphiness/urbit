=,  crypto
=<  crub
|%
++  crub
  ::!:
  ::^-  acru
  ::todo: because of rekeying, maybe we just have a whole separate field for
  ::original keys + tweak
  |_  $%  [tw=%| pub=[cry=@ sgn=@ ~] sek=$@(~ [cry=@ sgn=@ sed=@ ~])]
          $:  tw=%&  pub=[cry=@ sgn=@ unsgn=@ dat=@]
              sek=$@(~ [cry=@ sgn=@ sed=@ unsgn=@])
          ==
      ==
  +*  sam  +<
  ::                                                  ::  ++as:crub:crypto
  ++  as                                              ::
    |%
    ::                                                ::  ++sign:as:crub:
    ++  sign                                          ::
      |=  msg=@
      ^-  @ux
      (jam [(sigh msg) msg])
    ::                                                ::  ++sigh:as:crub:
    ++  sigh                                          ::
      |=  msg=@
      ^-  @ux
      ?~  sek  ~|  %pubkey-only  !!
      (sign-raw:ed msg sgn.pub sgn.sek)
    ::                                                ::  ++sure:as:crub:
    ++  sure                                          ::
      |=  txt=@
      ^-  (unit @ux)
      =+  ;;([sig=@ msg=@] (cue txt))
      ?.  (safe sig msg)  ~
      (some msg)
    ::                                                ::  ++safe:as:crub:
    ++  safe
      |=  [sig=@ msg=@]
      ^-  ?
      (veri:ed sig msg sgn.pub)
    ::                                                ::  ++seal:as:crub:
    ++  seal                                          ::
      |=  [bpk=pass msg=@]
      ^-  @ux
      ?~  sek  ~|  %pubkey-only  !!
      ?>  =('b' (end 3 bpk))
      =+  pk=(rsh 8 (rsh 3 bpk))
      =+  shar=(shax (shar:ed pk cry.sek))
      =+  smsg=(sign msg)
      (jam (~(en siva:aes shar ~) smsg))
    ::                                                ::  ++tear:as:crub:
    ++  tear                                          ::
      |=  [bpk=pass txt=@]
      ^-  (unit @ux)
      ?~  sek  ~|  %pubkey-only  !!
      ?>  =('b' (end 3 bpk))
      =+  pk=(rsh 8 (rsh 3 bpk))
      =+  shar=(shax (shar:ed pk cry.sek))
      =+  ;;([iv=@ len=@ cph=@] (cue txt))
      =+  try=(~(de siva:aes shar ~) iv len cph)
      ?~  try  ~
      (sure:as:(com:nu:..as bpk) u.try)
    --  ::as
  ::                                                  ::  ++de:crub:crypto
  ++  de                                              ::  decrypt
    |=  [key=@J txt=@]
    ^-  (unit @ux)
    =+  ;;([iv=@ len=@ cph=@] (cue txt))
    %^    ~(de sivc:aes (shaz key) ~)
        iv
      len
    cph
  ::                                                  ::  ++dy:crub:crypto
  ++  dy                                              ::  need decrypt
    |=  [key=@J cph=@]
    (need (de key cph))
  ::                                                  ::  ++en:crub:crypto
  ++  en                                              ::  encrypt
    |=  [key=@J msg=@]
    ^-  @ux
    (jam (~(en sivc:aes (shaz key) ~) msg))
  ::                                                  ::  ++ex:crub:crypto
  ++  ex                                              ::  extract
    |%
    ::                                                ::  ++fig:ex:crub:crypto
    ++  fig                                           ::  fingerprint
      ^-  @uvH
      (shaf %bfig pub)
    ::                                                ::  ++pac:ex:crub:crypto
    ++  pac                                           ::  private fingerprint
      ^-  @uvG
      ?~  sek  ~|  %pubkey-only  !!
      (end 6 (shaf %bcod sec))
    ::                                                ::  ++pub:ex:crub:crypto
    ++  pub                                           ::  public key
      ^-  pass
      (cat 3 'b' (cat 8 sgn.^pub cry.^pub))
    ::
    ++  tub
      ^-  pass
      ?>  ?=(%& tw)
      %^  cat  3  't'
      %+  can  8
      :~  [1 cry.pub.sam]
          [1 unsgn.pub.sam]
          [(met 8 dat.pub.sam) dat.pub.sam]
      ==
    ::                                                ::  ++sec:ex:crub:crypto
    ++  sec                                           ::  private key
      ^-  ring
      ?~  sek  ~|  %pubkey-only  !!
      ?:  ?=(%& -.sam)
        %^  cat  3  'T'
        %+  can  8
        :~  [1 cry.sek.sam]
            [1 sed.sek.sam]
            [(met 8 dat.pub.sam) dat.pub.sam]
        ==
      (cat 3 'B' (cat 8 sed.sek cry.sek))
    --  ::ex
  ::                                                  ::  ++nu:crub:crypto
  ++  nu                                              ::
    |%
    ::                                                ::  ++pit:nu:crub:crypto
    ++  pit                                           ::  create keypair
      |=  [w=@ seed=@]
      ^+  ..nu
      =+  wid=(add (div w 8) ?:(=((mod w 8) 0) 0 1))
      =+  bits=(shal wid seed)
      =+  [c=(rsh 8 bits) s=(end 8 bits)]
      =+  l=(luck:ed s)
      ..nu(+< [%| pub=[cry=(puck:ed c) sgn=pub.l ~] sek=[cry=c sgn=sec.l sed=s ~]])
    ::
    ++  wit                                           ::  create keypair
      |=  [w=@ seed=@ tw=@]
      ^+  ..nu
      =+  wid=(add (div w 8) ?:(=((mod w 8) 0) 0 1))
      =+  bits=(shal wid seed)
      =+  [c=(rsh 8 bits) s=(end 8 bits)]
      =+  l=(luck:ed s)
      =+  tl=(scad:ed pub.l sec.l (shax (can 0 ~[32^pub.l (met 0 tw)^tw])))
      =-  ..nu(+< -)
      :*  tw=%&  pub=[cry=(puck:ed c) sgn=pub.tl unsgn=pub.l dat=tw]
          sek=[cry=c sgn=sec.tl sed=s unsgn=sec.l]
          :: sek=$@(~ [cry=@ sgn=@ sed=@ unsgn=@])
      ==
    ::                                                ::  ++nol:nu:crub:crypto
    ++  nol                                           ::  activate secret
      |=  a=ring
      ^+  ..nu
      =+  [mag=(end 3 a) bod=(rsh 3 a)]
      ?:  =('B' mag)
        =+  [c=(rsh 8 bod) s=(end 8 bod)]
        =+  l=(luck:ed s)
        ..nu(+< [%| pub=[cry=(puck:ed c) sgn=pub.l ~] sek=[cry=c sgn=sec.l sed=s ~]])
      ::  todo: not proper tweak
      ~|  %not-crub-seckey  ?>  =('T' mag)
      =+  [c=(cut 8 [0 1] bod) s=(cut 8 [1 1] bod) d=(rsh [8 2] bod)]
      =+  l=(luck:ed s)
      =+  tl=(scad:ed pub.l sec.l (shax (can 0 ~[32^pub.l (met 0 d)^d])))
      =-  ..nu(+< -)
      :*  tw=%&  pub=[cry=(puck:ed c) sgn=pub.tl unsgn=pub.l dat=d]
          sek=[cry=c sgn=sec.tl sed=s unsgn=sec.l]
      ==
    ::                                                ::  ++com:nu:crub:crypto
    ++  com                                           ::  activate public
      |=  a=pass
      ^+  ..nu
      =+  [mag=(end 3 a) bod=(rsh 3 a)]
      ~|  %not-crub-pubkey 
      ?:  =('b' mag)
        ..nu(+< [%| pub=[cry=(rsh 8 bod) sgn=(end 8 bod) ~] sek=~])
      =+  [cry=(cut 8 [0 1] bod) unsgn=(cut 8 [1 1] bod) dat=(rsh [8 2] bod)]
      =+  sgn=(scap:ed:crypto unsgn (shax (can 0 ~[32^unsgn (met 0 dat)^dat])))
      ?.  =('t' mag)  !!
      ..nu(+< [%& pub=[cry sgn unsgn dat] sek=~])
    --  ::nu
  --  ::crub
::
++  trub                                            ::  test crub
  |=  msg=@t
  ::
  ::  make acru cores
  ::

  =/  ali      (pit:nu:crub 512 (shaz 'alice')) ::(shax 'tweak'))
  =/  ali-pub  (com:nu:crub pub:ex.ali)
  =/  bob      (wit:nu:crub 512 (shaz 'Robert') (shax 'tweak'))
  =/  bob-pub  (com:nu:crub pub:ex.bob)
  ::
  ::  alice signs and encrypts a symmetric key to bob
  ::
  =/  secret-key  %-  shaz
      'Let there be no duplicity when taking a stand against him.'
  =/  signed-key   (sign:as.ali secret-key)
  =/  crypted-key  (seal:as.ali pub:ex.bob-pub signed-key)
  ::  bob decrypts and verifies
  =/  decrypt-key-attempt  (tear:as.bob pub:ex.ali-pub crypted-key)
  =/  decrypted-key    ~|  %decrypt-fail  (need decrypt-key-attempt)
  =/  verify-key-attempt   (sure:as.ali-pub decrypted-key)
  =/  verified-key     ~|  %verify-fail  (need verify-key-attempt)
  ::  bob encrypts with symmetric key
  =/  crypted-msg  (en.bob verified-key msg)
  ::  alice decrypts with same key
  `@t`(dy.ali secret-key crypted-msg)
+$  hoop
  [sin=@uxI dex=@uxI chain=@uxI]
+$  fling  [pub=@ux chain=@uxI]
++  root-key  (swp 3 'ed25519 seed')
++  sha256
  |=  [k=@ m=@]
  (hmac-sha256:hmac k m)
++  root
  |=  eny=@uxI
  ^-  hoop
  :: ?>  =(512 (met 0 eny))
  =/  chain=@ux
    (sha256 root-key (cat 3 eny 1))
  =/  ext  (hmac-sha512:hmac root-key eny)
  =/  [sin=@uxI dex=@uxI]   [(rsh [3 32] ext) (end [3 32] ext)]
  =/  sine  (rip 3 sin)
  =/  match  (dis 0b10.0000 (snag 0 sine))
  ?.  =(0 match)
    ~|  weird-root/sine
    !!
  =.  sine  (snoc (snip sine) (dis 0b1111.1000 (rear sine)))
  =.  sine  (snap sine 0 (con 0b100.0000 (dis 0b111.1111 (snag 0 sine))))
  [(rep 3 sine) dex chain]
  ++  heir
  |=  [=fling i=@]
  ^+  fling
  =/  zed
    %+  hmac-sha512:hmac  chain.fling
    (cat 3 2 (cat 5 pub.fling i))
  =/  ai  (ward:ed (need (deco:ed pub.fling)) (scam:ed bb:ed (mul 8 (rsh [3 28] zed))))
  ?:  =([0 1] ai)
    !!
  :-  (etch:ed ai)
  %+  end  [3 32]
  %+  hmac-sha512:hmac  chain.fling
  (cat 3 3 (cat 5 pub.fling i))
  

++  chime
  |_  =hoop
  ++  fo  ~(. ^fo (bex 256))
  ++  pub   (etch:ed pubp)
  ++  pubp  (scam:ed bb:ed sin.hoop)
  ++  pub-two  `@ux`(scalarmult-base:ed `@`(swp 3 sin.hoop))
  ++  hmuc  (cury hmac-sha512:hmac chain.hoop)
  ++  fling  `^fling`[pub chain.hoop]
  ++  aspy
    |=  i=@ud
    ^+  hoop
    =/  zed
      %-  hmuc
      ?:  (lth i (bex 31))
        (cat 3 2 (cat 5 pub i))
      (cat 5 (cat 3 0 (cat 3 sin.hoop dex.hoop)) 0)
    =/  [sinz=@uxI dexz=@uxI]  [(cut 3 [0 28] zed) (end [3 32] zed)]
    :+  (sum:fo (pro:fo 8 sinz) sin.hoop)  (sum:fo dexz dex.hoop)
    %-  hmuc
    ?:  (lth i (bex 31))
      (cat 5 (cat 3 3 pub) i)
    (cat 5 (rep 3 1 sin.hoop dex.hoop ~) i)
  --
++  test-root
  =/  fst  
    (root 0x1a9f.da9c.f5bc.fb0e.36ec.e0b5.3e6a.f837.138e.b48a.d4d6.2df3.532e.4620.4199.9a13.5fb9.365b.d879.b581.5882.5acc.3388.ff44.1a58.8397.8a93.7fc0.004c.c59d.c877.4a8b)
  =/  snd
    :*  sin=0xe809.7bcd.9153.5a82.cfc5.1db7.67ad.2df4.997f.8b3a.629d.a4c8.1648.0ddb.c9b3.c152
        dex=0xae87.55ac.7fde.5218.a321.adf0.6d94.218c.878a.7f8f.449a.b83b.8a58.6e5d.64cd.ed58
        chain=0x9c14.2b78.1553.d575.d4e9.9f0f.781c.b879.cf7f.0176.0e61.a75c.9aac.b185.de7e.4015
    ==
  ?>  =(fst snd)
  ~
--
