# Repository-authored release selection shared by fetch.sh and build.sh.
release_text=$(python3 -I "$(dirname "${BASH_SOURCE[0]}")/release.py")
mapfile -t release_fields <<< "$release_text"
VERSION=${release_fields[0]}; ROOT=${release_fields[1]}
SHA256=${release_fields[2]}; URL=${release_fields[3]}
