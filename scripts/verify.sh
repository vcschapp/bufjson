#!/usr/bin/env bash

readonly -a tools=(clippy doc fmt build test)

readonly -A tool_commands=(
  [clippy]='env,RUSTFLAGS=-D warnings,cargo,clippy'
  [doc]='env,RUSTDOCFLAGS=-D warnings,cargo,doc'
  [fmt]='cargo,fmt,--check'
  [build]='env,RUSTFLAGS=-D warnings,cargo,build'
  [test]='env,RUSTFLAGS=-D warnings,cargo,test,--benches'
)

readonly -A profile_args=(
  [default]=""
  [release]="--release"
)

readonly -A tool_profiles=(
  [clippy]="default release"
  [doc]="default"
  [fmt]="default"
  [build]="default release"
  [test]="default release"
)

readonly -A feature_mix_args=(
  [default]=""
  [all]="--all-features"
  [benches]="--all-features"
)

readonly -A tool_feature_mixes=(
    [clippy]="default all"
    [doc]="default all"
    [fmt]="default"
    [build]="default all"
    [test]="default all"
)

function run_tool_quiet() {
  local -r tool="$1"
  local -r profile="$2"
  local -r feature_mix="$3"

  local -a cmd
  IFS=, read -r -a cmd <<<"${tool_commands[$tool]}"
  readonly cmd

  local -a args=(--quiet)
  if [ -n "${profile_args[$profile]}" ]; then
    args+=("${profile_args[$profile]}")
  fi
  if [ -n "${feature_mix_args[$feature_mix]}" ]; then
    args+=("${feature_mix_args[$feature_mix]}")
  fi

  printf "  profile: %s, feature mix: %s ... " "$profile" "$feature_mix"

  local exit_code=0
  if [[ "$tool" != test ]]; then
    "${cmd[@]}" "${args[@]}" || exit_code=$?
  else
    "${cmd[@]}" "${args[@]}" >/dev/null 2>&1 || exit_code=$?
  fi

  if [[ $exit_code == 0 ]]; then
    echo -e "\e[1m\e[32mok\e[0m"
    return 0
  else
    echo -e "\e[1m\e[31merror\e[0m: exited with code $exit_code"
    return 1
  fi
}

num_failures=0

for tool in "${tools[@]}"; do
  echo -e "\e[1m$tool\e[0m:"
  for profile in ${tool_profiles[$tool]}; do
    for feature_mix in ${tool_feature_mixes[$tool]}; do
      if ! run_tool_quiet "$tool" "$profile" "$feature_mix"; then
        num_failures=$((num_failures + 1))
      fi
    done
  done
done

if [[ $num_failures -gt 0 ]]; then
  exit 1
fi
