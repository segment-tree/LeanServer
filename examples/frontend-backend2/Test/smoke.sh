#!/usr/bin/env bash
set -euo pipefail

example_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
bin_dir="$example_dir/.lake/build/bin"
for service in frontend left right backend; do
  test -x "$bin_dir/$service" || { echo "Build the four services first" >&2; exit 1; }
done
for port in 8080 8081 8082 8083; do
  if (exec 3<>"/dev/tcp/127.0.0.1/$port") 2>/dev/null; then
    echo "Port $port is already occupied; no services started" >&2
    exit 1
  fi
done

smoke_dir=$(mktemp -d)
pids=()
cleanup() {
  for pid in "${pids[@]}"; do kill "$pid" 2>/dev/null || true; done
  for pid in "${pids[@]}"; do wait "$pid" 2>/dev/null || true; done
  rm -rf -- "$smoke_dir"
}
trap cleanup EXIT
for service in backend left right frontend; do
  "$bin_dir/$service" >"$smoke_dir/$service.log" 2>&1 &
  pid=$!
  pids+=("$pid")
  if [[ "$service" == left ]]; then left_pid=$pid; fi
done

for port in 8080 8081 8082 8083; do
  ready=false
  for attempt in {1..50}; do
    if curl --noproxy '*' -s -o /dev/null --max-time 1 "http://127.0.0.1:$port/resource"; then
      ready=true
      break
    fi
    sleep 0.1
  done
  if [[ "$ready" != true ]]; then
    cat "$smoke_dir"/*.log >&2
    exit 1
  fi
done

request() {
  local body=$1 expected_status=$2
  shift 2
  local status
  status=$(curl --noproxy '*' -sS --max-time 5 -X GET --data-binary "$body" \
    -o "$smoke_dir/body" -w '%{http_code}' "$@" http://127.0.0.1:8080/resource)
  [[ "$status" == "$expected_status" ]] || {
    echo "Expected $expected_status, received $status" >&2
    cat "$smoke_dir/body" >&2
    exit 1
  }
}
auth=(-H 'X-Username: Tom' -H 'X-Password: 123456')
expected_resource=$(curl --noproxy '*' -sS --max-time 5 http://127.0.0.1:8081/resource)
for body in a ab ''; do
  request "$body" 200 "${auth[@]}"
  [[ $(cat "$smoke_dir/body") == "$expected_resource" ]]
done
request a 401
request ab 401 -H 'X-Username: Tom' -H 'X-Password: wrong'
request a 401 "${auth[@]}" -H 'x-username: Tom'
echo 'PASS live services: odd/even/empty resource and credential rejection'

# Taking down only left distinguishes routing from a handler that always uses
# right or bypasses the relays. This is an IO test, outside the reliable graph theorem.
kill "$left_pid"
wait "$left_pid" 2>/dev/null || true
pids=("${pids[0]}" "${pids[2]}" "${pids[3]}")
request a 502 "${auth[@]}"
request ab 200 "${auth[@]}"
echo 'PASS live routing: left unavailable breaks odd requests; even requests still succeed'
