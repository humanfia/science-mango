from pathlib import Path
import json
p=Path('/home/jing/m7-lean-canonical-outer-formalization');b=Path('/home/jing/science-mango-quantum-harness-publish-20260914/pipelines/quantum_formalize/examples/m7/canonical_outer');source=(p/'M7CanonicalOuter.lean').read_text();q='M7.CanonicalOuter.';f='∀ (N : ℕ) [NeZero N], ';rc='M7.Action.Recipe N';rec='M7.Action.Record N';act='M7.Action.act';ca=q+'canonical';pk=q+'pairKey';ks=q+'keyset'
items=[
('pair_key_injective',[],f+'Function.Injective ('+pk+' (N := N))'),
('unit_index',[],f+'∀ (u : (ZMod N)ˣ) (e : Bool), ∃ i ∈ '+q+'indices N, '+q+'outerRecord i = (⟨u,e,0,0⟩ : '+rec+')'),
('indices_nonempty',['unit_index'],f+'('+q+'indices N).Nonempty'),
('choices_nonempty',['indices_nonempty'],f+'∀ c : '+rc+', ('+q+'choices c).Nonempty'),
('chosen_outer_member',['choices_nonempty'],f+'∀ c : '+rc+', '+q+'chosenOuter c ∈ '+q+'indices N'),
('canonical_key_agrees',['choices_nonempty'],f+'∀ c : '+rc+', (ofLex ('+q+'best c)).1 = '+pk+' ('+ca+' c)'),
('canonical_key_member',['chosen_outer_member'],f+'∀ c : '+rc+', '+pk+' ('+ca+' c) ∈ '+ks+' c'),
('canonical_minimal',['choices_nonempty','canonical_key_agrees'],f+'∀ (c : '+rc+') k, k ∈ '+ks+' c → '+pk+' ('+ca+' c) ≤ k'),
('realizer_correct',[],f+'∀ c : '+rc+', '+act+' ('+q+'realizer c) c = '+ca+' c'),
('realizer_inverse',['realizer_correct'],f+'∀ c : '+rc+', '+act+' (M7.Action.inverse ('+q+'realizer c)) ('+ca+' c) = c'),
('canonical_cards',[],f+'∀ (c : '+rc+') (w : ℕ), c.1.card = w → c.2.card = w → ('+ca+' c).1.card = w ∧ ('+ca+' c).2.card = w'),
('canonical_anchored',[],f+'∀ c : '+rc+', c.1.Nonempty → c.2.Nonempty → 0 ∈ ('+ca+' c).1 ∧ 0 ∈ ('+ca+' c).2'),
('normalize_act_shifts',[],f+'∀ (g : '+rec+') (c : '+rc+'), '+q+'normalizePair ('+act+' g c) = '+q+'normalizePair ('+act+' (⟨g.unit,g.exchange,0,0⟩ : '+rec+') c)'),
('keyset_all_records',['unit_index','normalize_act_shifts'],f+'∀ c : '+rc+', '+ks+' c = (Finset.univ : Finset ('+rec+')).image (fun g => '+pk+' ('+q+'normalizePair ('+act+' g c)))'),
('keyset_action',['keyset_all_records'],f+'∀ (g : '+rec+') (c : '+rc+'), '+ks+' ('+act+' g c) = '+ks+' c'),
('canonical_invariant',['pair_key_injective','canonical_key_member','canonical_minimal','keyset_action'],f+'∀ (g : '+rec+') (c : '+rc+'), '+ca+' ('+act+' g c) = '+ca+' c'),
('orbit_complete',['canonical_invariant','realizer_correct','realizer_inverse'],f+'∀ c d : '+rc+', (∃ g : '+rec+', '+act+' g c = d) ↔ '+ca+' c = '+ca+' d')]
g={'title':'M7 actual unit/exchange canonical representatives using separate block normalization','nodes':[{'id':i,'dependencies':deps,'spec':{'name':q+i,'statement':s,'imports':['M7CanonicalOuter'],'context':'','queries':['algebra'],'guidance':'Use frozen actual Record Group/MulAction and accepted CanonicalBlock13. indices only unit/exchange positions; shifts are found separately per block. Unit index is (Fin element of unit.val, Bool), with IsUnit.unit_spec. Minima use Prod.Lex.monotone_fst, not dependent cases on best. normalize_act_shifts follows Finset.image_image and normalize_shift; never unfold all normalize internals unnecessarily. keyset_all_records is a semantic proof identity only, not a replacement generation implementation. Group right multiplication is bijective, so keyset_action follows act_compose. canonical invariant follows two minima and pair key injectivity; orbit completeness uses retained realizing actions and inverse. Return tactic lines only.\n'+source}}for i,deps,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7CanonicalOuter\n'+''.join('def target_'+str(j)+' : Prop := '+s+'\n'for j,(_,_,s)in enumerate(items)))
(b/'SCOPE.md').write_text('# Actual outer canonical representative\n\nSeventeen exact targets complete the actual unit/exchange invariant on top of accepted separate block translation normalization. Candidate generation enumerates only unit/exchange indices and retains an actual realizing action/inverse. The full-record keyset appears only in a proof identity, never in the generation definition. Nonempty supports remain anchored and equal weights are preserved. Connectedness is handled by its separate original-domain bridge. No full M7 acceptance is claimed.\n');print('prepared17 concrete targets')
