/*******************************************************************\

Module: A special command line object for the ld-like options

Author: Daniel Kroening, 2013

\*******************************************************************/

/// \file
/// A special command line object for the ld-like options

#include "ld_cmdline.h"

#include <util/invariant.h>
#include <util/prefix.h>

#include <iostream>

// clang-format off
const char *goto_ld_options_with_argument[]=
{
  "--verbosity",
  "--native-compiler",
  "--native-linker",
  "--validate-goto-model",
  nullptr
};

const char *ld_options_with_argument[]=
{
  "-a",
  "--architecture",
  "-A",
  "--format",
  "-b",
  "--mri-script",
  "-c",
  "--entry",
  "-e",
  "--auxiliary",
  "-f",
  "--filter",
  "-F",
  "--gpsize",
  "-G",
  "--soname",
  "-h",
  "--dynamic-linker",
  "-I",
  "--library",
  "-l",
  "--library-path",
  "-L",
  "--sysroot",
  "-m",
  "--output",
  "-o",
  "-O",
  "--plugin",
  "--plugin-opt",
  "--flto-partition",
  "--just-symbols",
  "-R",
  "--script",
  "-T",
  "--default-script",
  "--dT",
  "--undefined",
  "-u",
  "--trace-symbol",
  "-y",
  "-Y",
  "--assert",
  "--defsym",
  "--file-alignment",
  "--fini",
  "--hash-size",
  "--heap",
  "--image-base",
  "--init",
  "--Map",
  "--major-image-version",
  "--major-os-version",
  "--major-subsystem-version",
  "--minor-image-version",
  "--minor-os-version",
  "--minor-subsystem-version",
  "--oformat",
  "--retain-symbols-file",
  "--rpath",
  "--rpath-link",
  "--section-alignment",
  "--sort-section",
  "--spare-dynamic-tags",
  "--stack",
  "--subsystem",
  "--task-link",
  "--section-start",
  "--Tbss",
  "--Tdata",
  "--Ttext",
  "--Ttext-segment",
  "--unresolved-symbols",
  "--version-exports-section",
  "--dynamic-list",
  "--wrap",
  "--hash-style",
  "-z",
  "--arch", // Apple only
  "--ios_version_min", // Apple only
  "--macosx_version_min", // Apple only
  "--install_name", // Apple only
  "--build-id",
  nullptr
};

const char *ld_options_without_argument[]=
{
  "--dc",
  "-d",
  "--dp",
  "--export-dynamic",
  "-E",
  "--no-export-dynamic",
  "--EB",
  "--EL",
  "-g",
  "--print-map",
  "-M",
  "--nmagic",
  "-n",
  "--omagic",
  "-N",
  "--no-omagic",
  "--flto",
  "--Qy",
  "--emit-relocs",
  "-q",
  "--relocatable",
  "-r",
  "-i",
  "--strip-all",
  "-s",
  "--strip-debug",
  "-S",
  "--strip-discarded",
  "--no-strip-discarded",
  "--trace",
  "-t",
  "--unique",
  "--Ur",
  "--version",
  "-v",
  "-V",
  "--discard-all",
  "-x",
  "--discard-locals",
  "-X",
  "--discard-none",
  "--start-group",
  "-(",
  "--end-group",
  "-)",
  "--accept-unknown-input-arch",
  "--no-accept-unknown-input-arch",
  "--add-needed",
  "--no-add-needed",
  "--as-needed",
  "--no-as-needed",
  "--Bdynamic",
  "--dy",
  "--call_shared",
  "--Bstatic",
  "--dn",
  "--non_shared",
  "--static",
  "--Bsymbolic",
  "--Bsymbolic-functions",
  "--check-sections",
  "--no-check-sections",
  "--copy-dt-needed-entries",
  "--no-copy-dt-needed-entries",
  "--cref",
  "--demangle",
  "--embedded-relocs",
  "--fatal-warnings",
  "--no-fatal-warnings",
  "--force-exe-suffix",
  "--gc-sections",
  "--no-gc-sections",
  "--print-gc-sections",
  "--no-print-gc-sections",
  "--help",
  "--no-define-common",
  "--no-demangle",
  "--no-keep-memory",
  "--no-undefined",
  "--allow-shlib-undefined",
  "--no-allow-shlib-undefined",
  "--allow-multiple-definition",
  "--no-undefined-version",
  "--default-symver",
  "--default-imported-symver",
  "--no-warn-mismatch",
  "--no-warn-search-mismatch",
  "--no-whole-archive",
  "--noinhibit-exec",
  "--noinhibit_exec",
  "--nostdlib",
  "--print-output-format",
  "--qmagic",
  "--reduce-memory-overheads",
  "--relax",
  "--no-relax",
  "--shared",
  "--Bshareable",
  "--pie",
  "--pic-executable",
  "--sort-common",
  "--sort_common",
  "--split-by-file",
  "--split-by-reloc",
  "--stats",
  "--target-help",
  "--traditional-format",
  "--verbose",
  "--dll-verbose",
  "--version-script",
  "--dynamic-list-data",
  "--dynamic-list-cpp-new",
  "--dynamic-list-cpp-typeinfo",
  "--warn-common",
  "--warn-constructors",
  "--warn-multiple-gp",
  "--warn-once",
  "--warn-section-align",
  "--warn-shared-textrel",
  "--warn-alternate-em",
  "--warn-unresolved-symbols",
  "--error-unresolved-symbols",
  "--whole-archive",
  "--build-id",
  "--eh-frame-hdr",
  "--enable-new-dtags",
  "--dylib", // Apple only
  "--dylinker", // Apple only
  "--bundle", // Apple only
  nullptr
};
// clang-format on

/// parses the command line options into a cmdlinet
/// \par parameters: argument count, argument strings
/// \return none
bool ld_cmdlinet::parse(int argc, const char **argv)
{
  PRECONDITION(argc > 0);
  add_arg(argv[0]);

  for(int i=1; i<argc; i++)
  {
    std::string argv_i=argv[i];

    // options file?
    if(has_prefix(argv_i, "@"))
    {
      // TODO
      continue;
    }

    // file?
    if(argv_i=="-" || !has_prefix(argv_i, "-"))
    {
      add_infile_arg(argv_i);
      continue;
    }

    bool found=false;

    for(const char **o=goto_ld_options_with_argument;
        *o!=nullptr && !found;
        ++o)
    {
      std::string os(*o);

      // separated?
      if(argv_i==os ||
         (os.size()>=3 && os[0]=='-' && os[1]=='-' && "-"+argv_i==os))
      {
        found=true;
        if(i!=argc-1)
        {
          set(os, argv[i+1]);
          i++;
        }
        else
        {
          std::cerr << "Warning: missing argument for " << argv_i << '\n';
          set(os, ""); // end of command line
        }
      }
      else if(os.size()>2 && has_prefix(argv_i, os+"=")) // concatenated, long
      {
        found=true;
        set(os, argv[i]+os.size()+1);
      }
    }

    // goto-ld-only command line argument found
    if(found)
      continue;

    // add to new_argv
    add_arg(argv_i);

    // also store in cmdlinet

    for(const char **o=ld_options_without_argument; *o!=nullptr && !found; o++)
    {
      std::string os(*o);
      // ld accepts all long options also as short option
      if(argv_i==os ||
         (os.size()>=3 && os[0]=='-' && os[1]=='-' && "-"+argv_i==os))
      {
        found=true;
        set(os); // record as long
      }
    }

    // arguments to options can be given as follows:
    // 1) concatenated for short options
    // 2) concatenated with '=' for long options
    // 3) separate

    for(const char **o=ld_options_with_argument; *o!=nullptr && !found; o++)
    {
      std::string os(*o);

      // separated?
      if(argv_i==os ||
         (os.size()>=3 && os[0]=='-' && os[1]=='-' && "-"+argv_i==os))
      {
        found=true;
        if(i!=argc-1)
        {
          set(os, argv[i+1]);
          add_arg(argv[i+1]);
          i++;
        }
        else
        {
          std::cerr << "Warning: missing argument for " << argv_i << '\n';
          set(os, ""); // end of command line
        }
      }
      else if(os.size()==2 && has_prefix(argv_i, os)) // concatenated, short
      {
        found=true;
        set(os, argv[i]+os.size());
      }
      else if(os.size()>2 && has_prefix(argv_i, os+"=")) // concatenated, long
      {
        found=true;
        set(os, argv[i]+os.size()+1);
      }
      // concatenated, long as short
      else if(os.size()>2 && has_prefix("-"+argv_i, os+"="))
      {
        found=true;
        set(os, argv[i]+os.size()+1-1);
      }
    }

    if(!found)
    {
      // unrecognized option
      std::cerr << "Warning: uninterpreted ld option '" << argv_i
                << "'\n";
    }
  }

  return false;
}
