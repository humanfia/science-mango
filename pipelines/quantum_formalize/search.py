"""Bounded LeanExplore retrieval, with separate receipts for both libraries."""
import asyncio
import json
from urllib.error import HTTPError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

API = 'https://www.leanexplore.com/api/v2/search'
PACKAGES = {'Mathlib': 'Mathlib', 'Physlib': 'Physlib'}


class SearchUnavailable(RuntimeError):
    pass


def _request(query, package, limit, timeout):
    request = Request(
        API + '?' + urlencode({'q': query, 'packages': package, 'limit': limit}),
        headers={'User-Agent': 'lean-explore/quantum-harness', 'Accept': 'application/json'},
    )
    try:
        with urlopen(request, timeout=timeout) as response:
            data = json.load(response)
    except HTTPError as error:
        raise SearchUnavailable(f'LeanExplore {package}: HTTP {error.code}') from None
    except (OSError, ValueError) as error:
        raise SearchUnavailable(f'LeanExplore {package}: {type(error).__name__}') from None
    # An ignored/unknown filter must not masquerade as successful library coverage.
    if data.get('packages_applied') != [package]:
        raise SearchUnavailable(f'LeanExplore did not confirm the {package} package filter')
    if not isinstance(data.get('results'), list):
        raise SearchUnavailable('LeanExplore returned an invalid result list')
    return data


async def search_both(queries, *, limit=5, timeout=30, request=_request):
    """Search both explicitly; errors differ from a valid zero-result response."""
    async def one(query, library, package):
        try:
            response = await asyncio.to_thread(request, query, package, limit, timeout)
            results = [{k: hit.get(k) for k in
                        ('id', 'name', 'module', 'source_link', 'source_text', 'docstring')}
                       for hit in response['results'][:limit]]
            return {'library': library, 'indexed_package': package, 'query': query,
                    'status': 'ok', 'results': results,
                    'packages_applied': response['packages_applied']}
        except SearchUnavailable as error:
            return {'library': library, 'indexed_package': package, 'query': query,
                    'status': 'unavailable', 'error': str(error), 'results': []}
    return await asyncio.gather(*(one(q, name, pkg) for q in queries
                                  for name, pkg in PACKAGES.items()))
