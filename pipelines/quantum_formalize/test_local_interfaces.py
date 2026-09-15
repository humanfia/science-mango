import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from .local_interfaces import local_interfaces

class LocalInterfaceTests(unittest.TestCase):
    def test_m6_import_headers_are_included_without_proof_bodies(self):
        result = self.collect({
            'M5Main.lean': 'import M6Cyclic\n',
            'M6Cyclic.lean': 'namespace M6.Cyclic\ntheorem helper : True := by trivial\nend M6.Cyclic\n',
        })
        self.assertEqual([f['module'] for f in result['files']], ['M5Main', 'M6Cyclic'])
        self.assertEqual(result['entries'][0]['namespace_context'], ['M6.Cyclic'])
        self.assertEqual(result['entries'][0]['header'], 'theorem helper : True')
        self.assertNotIn('trivial', str(result['entries']))

    def test_m7_headers_retain_m6_import_provenance_and_omit_bodies(self):
        result = self.collect({
            'M5Main.lean': 'import M7Selection\n',
            'M7Selection.lean': 'import M6Cyclic\nnamespace M7.Selection\ndef winner : Prop := True\nend M7.Selection\n',
            'M6Cyclic.lean': 'theorem legacy : True := by trivial\n',
        })
        self.assertEqual([f['module'] for f in result['files']],
                         ['M5Main', 'M7Selection', 'M6Cyclic'])
        self.assertEqual(result['entries'][0]['namespace_context'], ['M7.Selection'])
        self.assertEqual(result['entries'][0]['header'], 'def winner : Prop')
        self.assertNotIn('trivial', str(result['entries']))

    def collect(self, sources, **kwargs):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); hashes={}
            for name,source in sources.items():
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
                hashes[name]=hashlib.sha256(path.read_bytes()).hexdigest()
            return local_interfaces(root,['M5Main'],hashes,**kwargs)

    def test_recursive_imports_namespaces_multiline_and_no_proof_bodies(self):
        result=self.collect({'M5Main.lean':'import M5Dep\nnamespace M5\nsection\nnamespace Inner\ntheorem foo\n    (n : Nat) :\n    n = n := by\n  exact rfl\nend Inner\nend\nend M5\n',
                             'M5Dep.lean':'import M5Main\nimport Mathlib\ntheorem M5.actual : True := by\n  trivial\n'})
        self.assertEqual(len(result['files']),2)
        self.assertEqual(result['entries'][0]['namespace_context'],['M5','Inner'])
        self.assertIn('(n : Nat)',result['entries'][0]['header'])
        text=str(result['entries'])
        self.assertIn('M5.actual',text)
        self.assertNotIn('exact rfl',text)
        self.assertNotIn('trivial',text)
        self.assertTrue(result['entries'][0]['complete_header'])

    def test_comments_and_strings_do_not_create_imports_or_headers(self):
        result=self.collect({'M5Main.lean':'/- namespace Bad\n/- nested -/\ntheorem fake : False := by\n-/\n-- import M5Fake\ndef message : String := "secret theorem"\ntheorem real : True := by trivial\n'})
        text=str(result)
        self.assertNotIn('fake',text)
        self.assertNotIn('secret',text)
        self.assertEqual(len(result['entries']),2)

    def test_bounds_and_incomplete_headers_are_explicit(self):
        result=self.collect({'M5Main.lean':'import M5Dep\ntheorem first (n : Nat) :\n  n = n := by rfl\ntheorem second : True := by trivial\n','M5Dep.lean':'theorem third : True := by trivial\n'},max_files=1,max_entries=1,max_header_chars=15,max_chars=15)
        self.assertEqual(len(result['files']),1)
        self.assertLessEqual(sum(len(x['header']) for x in result['entries']),15)
        self.assertFalse(result['entries'][0]['complete_header'])
        self.assertIn('incomplete',result['entries'][0]['note'])
        self.assertTrue(result['truncated'])

    def test_let_binding_and_default_binder_are_incomplete_excerpts(self):
        result=self.collect({'M5Main.lean':'theorem foo : ∀ n : Nat, let k := n; k = k := by simp\ntheorem bar (n : Nat := 0) : n = n := by rfl\n'})
        self.assertEqual(len(result['entries']),2)
        self.assertTrue(all(not e['complete_header'] for e in result['entries']))
        self.assertTrue(all('incomplete' in e['note'] for e in result['entries']))
        self.assertNotIn('by simp',str(result['entries']))

    def test_serialized_reference_budget(self):
        result=self.collect({'M5Main.lean':'namespace M5\n'+''.join(f'theorem t{i} : True := by trivial\n' for i in range(80))+'end M5\n'},max_prompt_chars=2000)
        self.assertLessEqual(len(json.dumps(result,ensure_ascii=False)),2000)
        self.assertTrue(result['truncated'])

    def test_hash_mismatch_and_nonfingerprinted_sources(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'M5Main.lean').write_text('theorem ok : True := by trivial')
            with self.assertRaises(ValueError):local_interfaces(root,['M5Main'],{'M5Main.lean':'wrong'})
            result=local_interfaces(root,['M5Main'],{})
            self.assertEqual(result['files'],[])
            self.assertEqual(result['entries'],[])


class PromptInterfaceTests(unittest.IsolatedAsyncioTestCase):
    async def test_controller_records_interfaces_without_changing_frozen_spec(self):
        from .engine import Spec, Draft, run, digest
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'lean-toolchain').write_text('leanprover/lean4:test')
            (root/'lakefile.toml').write_text('name = "test"')
            (root/'M5Main.lean').write_text('namespace M5.Real\ntheorem helper : True := by trivial\nend M5.Real\n')
            spec=Spec(name='M5.target',statement='True',imports=['M5Main'],queries=['test'])
            original=spec.model_dump();prompts=[]
            async def search(queries):return [{'library':lib,'status':'ok'} for lib in ['Mathlib','Physlib']]
            async def propose(prompt,attempt):prompts.append(prompt);return Draft(proof='exact True.intro')
            def checker(target,proof,project,attempt,timeout):
                self.assertEqual(target.model_dump(),original)
                return {'accepted':True,'stage':'acceptance','axioms':[]}
            result=await run(spec,root,propose,search=search,checker=checker,build=False)
            reference=json.loads((Path(result['work'])/'local-interfaces.json').read_text())
            self.assertEqual(result['local_interfaces_sha256'],digest(reference))
            self.assertIn('M5.Real',prompts[0]);self.assertIn('theorem helper : True',prompts[0])
            self.assertNotIn('by trivial',prompts[0])
            self.assertEqual(json.loads((Path(result['work'])/'spec.json').read_text()),original)

if __name__=='__main__':unittest.main()
