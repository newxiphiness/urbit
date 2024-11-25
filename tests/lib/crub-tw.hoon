/+  crub=crub-tw, *test
|%
++  tweak   %the-time-is-out-of-joint
+$  typ
$%  [tw=%| pub=[cry=@ux sgn=@ux ~] sek=$@(~ [cry=@ux sgn=@ux sed=@ux ~])]
          $:  tw=%&  pub=[cry=@ux sgn=@ux unsgn=@ux dat=@ux]
              sek=$@(~ [cry=@ux sgn=@ux sed=@ux unsgn=@ux])
          ==
      ==

++  run-bijective
  |=  eny=@uvJ
  =+  cub=(wit:nu:crub 512 eny tweak)
  =/  sec=ring   sec:ex:cub
::~&  want/`typ`+<:cub
::~&  have/`typ`+<:(nol:nu:crub sec)
  (expect-eq !>(`typ`+<:cub) !>(`typ`+<:(nol:nu:crub sec)))
++  test-bijective
  %-  zing
  %+  turn  (gulf 0 100)
  |=  i=@
  (run-bijective (shaz i))
--
