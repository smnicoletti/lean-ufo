# Optional pinned dependency sources

`dependency-sources.tar.gz` contains clean, shallow Git checkouts at every
revision in `lake-manifest.json`. It contains source and license files, not
host-compiled Lean caches. The source distribution can include this generated
archive to avoid fetching dependency repositories during a Docker build.

Without this archive, the Dockerfile fetches the pinned dependency revisions
over the network. Reviewers using a saved image need neither this archive nor
network access for the documented batch commands.
