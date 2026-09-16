from pathlib import Path
import json,hashlib,shutil

def reuse_verified_caches(project, cache_sources):
 project=Path(project);records=[]
 sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
 for source in cache_sources:
  source=Path(source);cache=source/'.lake/build'
  if not cache.exists():continue
  if (source/'lean-toolchain').read_bytes()!=(project/'lean-toolchain').read_bytes():
   records.append({'source_project':str(source),'skipped':'toolchain differs; perform normal child build'});continue
  source_manifest=json.loads((source/'lake-manifest.json').read_text());target_manifest=json.loads((project/'lake-manifest.json').read_text())
  if source_manifest['packages']!=target_manifest['packages']:
   records.append({'source_project':str(source),'skipped':'package manifest differs; perform normal child build'});continue
  shutil.copytree(cache,project/'.lake/build',dirs_exist_ok=True)
  matched={};invalidated={}
  for child in project.glob('*.lean'):
   original=source/child.name
   if original.exists() and sha(original)==sha(child):matched[child.name]=sha(child);continue
   invalidated[child.name]={'source_sha256':sha(original) if original.exists() else None,'child_sha256':sha(child),'reason':'Different or missing same-name source; delete copied module outputs so normal Lake compilation is mandatory'}
   for directory in [project/'.lake/build/lib/lean',project/'.lake/build/ir']:
    if directory.exists():
     for artifact in directory.glob(child.stem+'.*'):
      if artifact.is_file():artifact.unlink()
  records.append({'source_project':str(source),'toolchain':(source/'lean-toolchain').read_text().strip(),'source_manifest_sha256':sha(source/'lake-manifest.json'),'same_source_sha256':matched,'invalidated_modules':invalidated})
 return {'sources':records,'child_full_lake_build_and_closed_target_preflight_required':True,'cached_acceptance_never_counts_as_new_target_proof':True}
