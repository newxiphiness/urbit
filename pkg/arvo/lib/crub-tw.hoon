|%
  ++  crub
    =,  crypto
    ::!:
    ::^-  acru
    ::todo: because of rekeying, maybe we just have a whole separate field for
    ::original keys + tweak
    |_  $%  [tw=%| pub=[cry=@ sgn=@ ~] sek=$@(~ [cry=@ sgn=@ sed=@ ~])]
            $:  tw=%&  pub=[cry=@ sgn=@ unsgn=@ sig=@ unsig=@ dat=@]
                sek=$@(~ [cry=@ sgn=@ sed=@ unsgn=@])
            ==
        ==
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
      ::                                                ::  ++sec:ex:crub:crypto
      ++  sec                                           ::  private key
        ^-  ring
        ?~  sek  ~|  %pubkey-only  !!
        (cat 3 'B' (cat 8 sgn.sek cry.sek))
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
      ++  tit                                           ::  create keypair
        |=  [w=@ seed=@ tw=@]
        ^+  ..nu
        =+  wid=(add (div w 8) ?:(=((mod w 8) 0) 0 1))
        =+  bits=(shal wid seed)
        =+  [c=(rsh 8 bits) s=(end 8 bits)]
        =+  l=(luck:ed s)
        =+  tl=(scad:ed pub.l sec.l (shax tw)) 
        ..nu(+< [%| pub=[cry=(puck:ed c) sgn=pub.tl ~] sek=[cry=c sgn=sec.tl sed=s ~]])
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
        =+  [c=(rsh 8 bod) s=(cut 8 [1 1] bod) d=(rsh [8 2] bod)]
        =+  l=(luck:ed s)
        =+  tl=(scad:ed pub.l sec.l (shax d))
        ..nu(+< [%| pub=[cry=(puck:ed c) sgn=pub.l ~] sek=[cry=c sgn=sec.l sed=s ~]])
        ::..nu(+< [%& pub=[cry=(puck:ed c) sgn=pub.l ~] sek=[cry=c sgn=sec.l sed=s ~]])
      ::                                                ::  ++com:nu:crub:crypto
      ++  com                                           ::  activate public
        |=  a=pass
        ^+  ..nu
        =+  [mag=(end 3 a) bod=(rsh 3 a)]
        ~|  %not-crub-pubkey  ?>  =('b' mag)
        ..nu(+< [%| pub=[cry=(rsh 8 bod) sgn=(end 8 bod) ~] sek=~])
      --  ::nu
    --  ::crub
    ::
    ++  trub                                            ::  test crub
      |=  msg=@t
      ::
      ::  make acru cores
      ::

      =/  ali      (tit:nu:crub 512 (shaz 'Alice')) ::(shax 'tweak'))
      =/  ali-pub  (com:nu:crub pub:ex.ali)
      =/  bob      (pit:nu:crub 512 (shaz 'Robert') (shax 'tweak'))
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
--
