import LEANprj._02Sequences.Theorems.ExistsNIPOfCauchyConv
import LEANprj._02Sequences.Theorems.ConvergesToOfBddMono
import LEANprj._02Sequences.Theorems.BWOfMonoConv
import LEANprj._02Sequences.Theorems.CauchyConvOfBW


theorem ax_sup_iff_ax_bw :
  AxSup ↔ AxBW :=
by
  constructor
  · intro ax_sup
    apply bw_of_monoconv
    apply convergesTo_of_bdd_mono
    exact ax_sup
  · intro ax_bw
    apply sup_unique
    apply exists_nip_of_cauchy_conv
    apply cauchy_conv_of_bw
    exact ax_bw
