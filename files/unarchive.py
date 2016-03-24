#!/usr/bin/python
# -*- coding: utf-8 -*-

# (c) 2012, Michael DeHaan <michael.dehaan@gmail.com>
# (c) 2013, Dylan Martin <dmartin@seattlecentral.edu>
# (c) 2015, Toshio Kuratomi <tkuratomi@ansible.com>
# (c) 2016, Dag Wieers <dag@wieers.com>
#
# This file is part of Ansible
#
# Ansible is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# Ansible is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with Ansible.  If not, see <http://www.gnu.org/licenses/>.

DOCUMENTATION = '''
---
module: unarchive
version_added: 1.4
short_description: Unpacks an archive after (optionally) copying it from the local machine.
extends_documentation_fragment: files
description:
     - The M(unarchive) module unpacks an archive. By default, it will copy the source file from the local system to the target before unpacking - set copy=no to unpack an archive which already exists on the target..
options:
  src:
    description:
      - If copy=yes (default), local path to archive file to copy to the target server; can be absolute or relative. If copy=no, path on the target server to existing archive file to unpack.
      - If copy=no and src contains ://, the remote machine will download the file from the url first. (version_added 2.0)
    required: true
    default: null
  dest:
    description:
      - Remote absolute path where the archive should be unpacked
    required: true
    default: null
  copy:
    description:
      - "If true, the file is copied from local 'master' to the target machine, otherwise, the plugin will look for src archive at the target machine."
    required: false
    choices: [ "yes", "no" ]
    default: "yes"
  creates:
    description:
      - a filename, when it already exists, this step will B(not) be run.
    required: no
    default: null
    version_added: "1.6"
  list_files:
    description:
      - If set to True, return the list of files that are contained in the tarball.
    required: false
    choices: [ "yes", "no" ]
    default: "no"
    version_added: "2.0"
  exclude:
    description:
      - List the directory and file entries that you would like to exclude from the unarchive action.
    required: false
    default: []
    version_added: "2.1"
  keep_newer:
    description:
      - Do not replace existing files that are newer than files from the archive.
    required: false
    default: no
    version_added: "2.1"
  extra_opts:
    description:
      - Specify additional options by passing in an array.
    default:
    required: false
    version_added: "2.1"
author: "Dylan Martin (@pileofrogs)"
todo:
    - detect changed/unchanged for .zip files
    - implement CRC32 support for .zip files
    - handle common unarchive args, like preserve owner/timestamp etc...
    - rewrite gtar implementation wrt. file_common_args (and owner/group/mode)
    - re-implement the zip support using native zipfile module
    - implement check-mode
    - implement diff-mode
notes:
    - requires C(gtar)/C(unzip) command on target host
    - can handle I(gzip), I(bzip2) and I(xz) compressed as well as uncompressed tar files
    - detects type of archive automatically
    - uses tar's C(--diff arg) to calculate if changed or not. If this C(arg) is not
      supported, it will always unpack the archive
    - existing files/directories in the destination which are not in the archive
      are not touched.  This is the same behavior as a normal archive extraction
    - existing files/directories in the destination which are not in the archive
      are ignored for purposes of deciding if the archive should be unpacked or not
'''

EXAMPLES = '''
# Example from Ansible Playbooks
- unarchive: src=foo.tgz dest=/var/lib/foo

# Unarchive a file that is already on the remote machine
- unarchive: src=/tmp/foo.zip dest=/usr/local/bin copy=no

# Unarchive a file that needs to be downloaded (added in 2.0)
- unarchive: src=https://example.com/example.zip dest=/usr/local/bin copy=no
'''

import re
import os
import stat
import pwd
import grp
import datetime
import time
from zipfile import ZipFile

# String from tar that shows the tar contents are different from the
# filesystem
OWNER_DIFF_RE = re.compile(r': Uid differs$')
GROUP_DIFF_RE = re.compile(r': Gid differs$')
MODE_DIFF_RE = re.compile(r': Mode differs$')
MODE_DIFF_RE = re.compile(r' is newer or same age.$')
MISSING_FILE_RE = re.compile(r': Warning: Cannot stat: No such file or directory$')
ZIP_FILE_MODE_RE = re.compile(r'([r-][w-][stx-]){3}')
# When downloading an archive, how much of the archive to download before
# saving to a tempfile (64k)
BUFSIZE = 65536

class UnarchiveError(Exception):
    pass

# class to handle .zip files
class ZipArchive(object):

    def __init__(self, src, dest, file_args, module):
        self.src = src
        self.dest = dest
        self.file_args = file_args
        self.opts = module.params['extra_opts']
        self.module = module
        self.excludes = module.params['exclude']
        self.includes = []
        self.cmd_path = self.module.get_bin_path('unzip')
        self._files_in_archive = []

    def _permstr_to_octal(self, modestr):
        ''' Convert a Unix permission string (rw-r--r--) into a mode (0644) '''
        revstr = modestr[::-1]
        mode = 0
        for j in range(0, 3):
            for i in range(0, 3):
                if revstr[i+3*j] in ['r', 'w', 'x', 's', 't']:
                    mode += 2**(i+3*j)
        # The unzip utility does not support setting the stST bits
#                if revstr[i+3*j] in ['s', 't', 'S', 'T' ]:
#                    mode += 2**(9+j)
        return mode

    @property
    def files_in_archive(self, force_refresh=False):
        if self._files_in_archive and not force_refresh:
            return self._files_in_archive

        self._files_in_archive = []
        archive = ZipFile(self.src)
        try:
            for member in archive.namelist():
                if member not in self.excludes:
                    self._files_in_archive.append(member)
        except:
            archive.close()
            raise UnarchiveError('Unable to list files in the archive')

        archive.close()
        return self._files_in_archive

    def is_unarchived(self):
        # TODO: It is possible to extract the CRC32 of each file and compare that
        #       Problem is that parsing the unzip -Zv info is going to be ugly
        cmd = '%s -ZT -s "%s"' % (self.cmd_path, self.src)
        if self.excludes:
            cmd += '-x ' + ' '.join(self.excludes)
        rc, out, err = self.module.run_command(cmd)

        old_out = out
        diff = ''
        if rc == 0:
            output = ''
            unarchived = True
        else:
            output = out
            unarchived = False

        for line in old_out.splitlines():
            change = False

            pcs = line.split()
            if len(pcs) != 8: continue

            ftype = pcs[0][0]
            permstr = pcs[0][1:10]
            size = int(pcs[3])
            path = pcs[7]

            # Skip excluded files
            if path in self.excludes:
                continue

            # Itemized change requires L for symlink
            if ftype == 'l':
                ftype = 'L'
            elif ftype == '-':
                ftype = 'f'

            # Bug in unzip output translates MS-DOS file attributes to incorrect string
            if len(permstr) == 6:
                if permstr == 'rw----':
                    permstr = 'rw-rw-r--'
                elif permstr == 'rwx---':
                    permstr = 'rwxrwxr-x'

            # Test string conformity
            if len(permstr) != 9 or not ZIP_FILE_MODE_RE.match(permstr):
                raise UnarchiveError('ZIP info perm format incorrect, %s' % permstr)

#            err += "%s%s %10d %s\n" % (ftype, permstr, size, path)
            dest = os.path.join(self.dest, path)
            try:
                st = os.lstat(dest)
            except Exception as e:
                change = True
                self.includes.append(path)
                err += 'Path %s is missing\n' % path
                diff += '>%s++++++.?? %s\n' % (ftype, path)
                continue

            if ftype == 'd' and not stat.S_ISDIR(st.st_mode):
                change = True
                self.includes.append(path)
                err += 'File %s already exists, but not as a directory\n' % path
                diff += 'c%s++++++.?? %s\n' % (ftype, path)
                continue

            if ftype == 'f' and not stat.S_ISREG(st.st_mode):
                change = True
                unarchived = False
                self.includes.append(path)
                err += 'Directory %s already exists, but not as a regular file\n' % path
                diff += 'c%s++++++.?? %s\n' % (ftype, path)
                continue

            if ftype == 'L' and not stat.S_ISLNK(st.st_mode):
                change = True
                self.includes.append(path)
                err += 'Directory %s already exists, but not as a symlink\n' % path
                diff += 'c%s++++++.?? %s\n' % (ftype, path)
                continue

            itemized = bytearray('.%s.......??' % ftype)

            dt_object = datetime.datetime(*(time.strptime(pcs[6], '%Y%m%d.%H%M%S')[0:6]))
            timestamp = time.mktime(dt_object.timetuple())

            # We do not compare directory mtime, since it changes with updates
            if self.module.params['keep_newer']:
                if stat.S_ISREG(st.st_mode) and timestamp > st.st_mtime:
                    change = True
                    self.includes.append(path)
                    err += 'File %s is older, replacing file\n' % path
                    itemized[4] = 't'
                elif stat.S_ISREG(st.st_mode) and timestamp < st.st_mtime:
                    # Add to excluded files, ignore other changes
                    out += 'File %s is newer, excluding file\n' % path
                    continue
            else:
                if stat.S_ISREG(st.st_mode) and timestamp != st.st_mtime:
                    change = True
                    self.includes.append(path)
                    err += 'File %s differs in mtime (%f vs %f)\n' % (path, timestamp, st.st_mtime)
                    itemized[4] = 't'

            if stat.S_ISREG(st.st_mode) and size != st.st_size:
                change = True
                err += 'File %s differs in size (%d vs %d)\n' % (path, size, st.st_size)
                itemized[3] = 's'

            mode = self._permstr_to_octal(permstr)

#            diff += "Path %s compare %o vs %o\n" % (path, mode, stat.S_IMODE(st.st_mode))
            if self.file_args['mode']:
                if self.file_args['mode'] != stat.S_IMODE(st.st_mode):
                    change = True
                    err += 'Path %s differs in permissions (%o vs %o)\n' % (path, self.file_args['mode'], stat.S_IMODE(st.st_mode))
                    itemized[5] = 'p'
            else:
                if mode != stat.S_IMODE(st.st_mode):
                    change = True
                    itemized[5] = 'p'
                    err += 'Path %s differs in permissions (%o vs %o)\n' % (path, mode, stat.S_IMODE(st.st_mode))

            if self.file_args['owner']:
                try:
                    owner = pwd.getpwuid(st.st_uid).pw_name
                except Exception as e:
                    owner = st.st_uid
                if self.file_args['owner'] != owner:
                    change = True
                    err += 'Path %s is owned by user %s, not by user %s as expected\n' % (path, owner, self.file_args['owner'])
                    itemized[6] = 'o'

            if self.file_args['group']:
                try:
                    group = pwd.getpwuid(st.st_uid).pw_name
                except Exception as e:
                    group = st.st_uid
                if self.file_args['group'] != group:
                    change = True
                    err += 'Path %s is owned by group %s, not by group %s as expected\n' % (path, group, self.file_args['group'])
                    itemized[6] = 'g'

            if change:
                if path not in self.includes:
                    self.includes.append(path)
                diff += '%s %s\n' % (itemized, path)

        if self.includes:
            unarchived = False

        return dict(unarchived=unarchived, rc=rc, out=out, err=err, cmd=cmd, diff=diff)

    def unarchive(self):
        cmd = '%s -o "%s"' % (self.cmd_path, self.src)
        if self.opts:
            cmd += ' ' + ' '.join(self.opts)
        if self.excludes:
            cmd += ' -x ' + ' '.join(self.excludes)
        if self.includes:
            cmd += ' ' + ' '.join(self.excludes)
        cmd += ' -d "%s"' % self.dest
        rc, out, err = self.module.run_command(cmd)
        return dict(cmd=cmd, rc=rc, out=out, err=err)

    def can_handle_archive(self):
        if not self.cmd_path:
            return False
        cmd = '%s -l "%s"' % (self.cmd_path, self.src)
        rc, out, err = self.module.run_command(cmd)
        if rc == 0:
            return True
        return False


# class to handle gzipped tar files
class TgzArchive(object):

    def __init__(self, src, dest, file_args, module):
        self.src = src
        self.dest = dest
        self.file_args = file_args
        self.opts = module.params['extra_opts']
        self.module = module
        self.excludes = [ path.rstrip('/') for path in self.module.params['exclude']]
        # Prefer gtar (GNU tar) as it supports the compression options -zjJ
        self.cmd_path = self.module.get_bin_path('gtar', None)
        if not self.cmd_path:
            # Fallback to tar
            self.cmd_path = self.module.get_bin_path('tar')
        self.zipflag = 'z'
        self._files_in_archive = []

    @property
    def files_in_archive(self, force_refresh=False):
        if self._files_in_archive and not force_refresh:
            return self._files_in_archive

        cmd = '%s -t%s' % (self.cmd_path, self.zipflag)
        if self.opts:
            cmd += ' ' + ' '.join(self.opts)
        if self.excludes:
            cmd += ' --exclude=' + ' --exclude='.join(self.excludes)
        cmd += ' -f "%s"' % self.src
        rc, out, err = self.module.run_command(cmd)
        if rc != 0:
            raise UnarchiveError('Unable to list files in the archive')

        for filename in out.splitlines():
            if filename and filename not in self.excludes:
                self._files_in_archive.append(filename)
        return self._files_in_archive

    def is_unarchived(self):
        cmd = '%s -C "%s" -d%s' % (self.cmd_path, self.dest, self.zipflag)
        if self.opts:
            cmd += ' ' + ' '.join(self.opts)
        if self.file_args['owner']:
            cmd += ' --owner="%s"' % self.file_args['owner']
        if self.file_args['group']:
            cmd += ' --group="%s"' % self.file_args['group']
        if self.file_args['mode']:
            cmd += ' --mode="%s"' % self.file_args['mode']
        if self.module.params['keep_newer']:
            cmd += ' --keep-newer-files'
        if self.excludes:
            cmd += ' --exclude=' + ' --exclude='.join(self.excludes)
        cmd += ' -f "%s"' % self.src
        rc, out, err = self.module.run_command(cmd)
        diff = ''
        # Check whether the differences are in something that we're
        # setting anyway

        # What is different
        unarchived = True
        old_out = out
        out = ''
        for line in old_out.splitlines() + err.splitlines():
            # FIXME: if we are extracting as a user, we should not assume a different user is a change
            if not self.file_args['owner'] and OWNER_DIFF_RE.search(line):
                out += line + '\n'
            # FIXME: if we are extracting as a user, we should not assume a different group is a change
            if not self.file_args['group'] and GROUP_DIFF_RE.search(line):
                out += line + '\n'
            if not self.file_args['mode'] and MODE_DIFF_RE.search(line):
                out += line + '\n'
            if MISSING_FILE_RE.search(line):
                out += line + '\n'
        if out:
            unarchived = False
        return dict(unarchived=unarchived, rc=rc, out=out, err=err, cmd=cmd)

    def unarchive(self):
        cmd = '%s -C "%s" -x%s' % (self.cmd_path, self.dest, self.zipflag)
        if self.opts:
            cmd += ' ' + ' '.join(self.opts)
        if self.module.params['keep_newer']:
            cmd += ' --keep-newer-files'
        if self.file_args['owner']:
            cmd += ' --owner="%s"' % self.file_args['owner']
        if self.file_args['group']:
            cmd += ' --group="%s"' % self.file_args['group']
        if self.file_args['mode']:
            cmd += ' --mode="%s"' % self.file_args['mode']
        if self.excludes:
            cmd += ' --exclude=' + ' --exclude='.join(self.excludes)
        cmd += ' -f "%s"' % (self.src)
        rc, out, err = self.module.run_command(cmd, cwd=self.dest)
        return dict(cmd=cmd, rc=rc, out=out, err=err)

    def can_handle_archive(self):
        if not self.cmd_path:
            return False

        try:
            if self.files_in_archive:
                return True
        except UnarchiveError:
            pass
        # Errors and no files in archive assume that we weren't able to
        # properly unarchive it
        return False


# class to handle tar files that aren't compressed
class TarArchive(TgzArchive):
    def __init__(self, src, dest, file_args, module):
        super(TarArchive, self).__init__(src, dest, file_args, module)
        self.zipflag = ''


# class to handle bzip2 compressed tar files
class TarBzipArchive(TgzArchive):
    def __init__(self, src, dest, file_args, module):
        super(TarBzipArchive, self).__init__(src, dest, file_args, module)
        self.zipflag = 'j'


# class to handle xz compressed tar files
class TarXzArchive(TgzArchive):
    def __init__(self, src, dest, file_args, module):
        super(TarXzArchive, self).__init__(src, dest, file_args, module)
        self.zipflag = 'J'


# try handlers in order and return the one that works or bail if none work
def pick_handler(src, dest, file_args, module):
    handlers = [TgzArchive, ZipArchive, TarArchive, TarBzipArchive, TarXzArchive]
    for handler in handlers:
        obj = handler(src, dest, file_args, module)
        if obj.can_handle_archive():
            return obj
    module.fail_json(msg='Failed to find handler for "%s". Make sure the required command to extract the file is installed.' % src)


def main():
    module = AnsibleModule(
        # not checking because of daisy chain to file module
        argument_spec = dict(
            src               = dict(required=True),
            original_basename = dict(required=False), # used to handle 'dest is a directory' via template, a slight hack
            dest              = dict(required=True),
            copy              = dict(default=True, type='bool'),
            creates           = dict(required=False),
            list_files        = dict(required=False, default=False, type='bool'),
            keep_newer        = dict(required=False, default=False, type='bool'),
            exclude           = dict(requited=False, default=[], type='list'),
            extra_opts        = dict(required=False, default=[], type='list'),
        ),
        add_file_common_args = True,
#        supports_check_mode = True,
    )

    src    = os.path.expanduser(module.params['src'])
    dest   = os.path.expanduser(module.params['dest'])
    file_args = module.load_file_common_arguments(module.params)
    copy   = module.params['copy']
    # did tar file arrive?
    if not os.path.exists(src):
        if copy:
            module.fail_json(msg="Source '%s' failed to transfer" % src)
        # If copy=false, and src= contains ://, try and download the file to a temp directory.
        elif '://' in src:
            tempdir = os.path.dirname(os.path.realpath(__file__))
            package = os.path.join(tempdir, str(src.rsplit('/', 1)[1]))
            try:
                rsp, info = fetch_url(module, src)
                # If download fails, raise a proper exception
                if rsp is None:
                    raise Exception(info['msg'])
                f = open(package, 'w')
                # Read 1kb at a time to save on ram
                while True:
                    data = rsp.read(BUFSIZE)

                    if data == "":
                        break # End of file, break while loop

                    f.write(data)
                f.close()
                src = package
            except Exception, e:
                module.fail_json(msg="Failure downloading %s, %s" % (src, e))
        else:
            module.fail_json(msg="Source '%s' does not exist" % src)
    if not os.access(src, os.R_OK):
        module.fail_json(msg="Source '%s' not readable" % src)

    # skip working with 0 size archives
    try:
        if os.path.getsize(src) == 0:
            module.fail_json(msg="Invalid archive '%s', the file is 0 bytes" % src)
    except Exception, e:
        module.fail_json(msg="Source '%s' not readable" % src)

    # is dest OK to receive tar file?
    if not os.path.isdir(dest):
        module.fail_json(msg="Destination '%s' is not a directory" % dest)

    handler = pick_handler(src, dest, file_args, module)

    res_args = dict(handler=handler.__class__.__name__, dest=dest, src=src)

    # do we need to do unpack?
    res_args['check_results'] = handler.is_unarchived()
    if res_args['check_results']['unarchived']:
        res_args['changed'] = False
    else:
        # do the unpack
        try:
            res_args['extract_results'] = handler.unarchive()
            if res_args['extract_results']['rc'] != 0:
                module.fail_json(msg="failed to unpack %s to %s" % (src, dest), **res_args)
        except IOError:
            module.fail_json(msg="failed to unpack %s to %s" % (src, dest))
        else:
            res_args['changed'] = True

    # Run only if we found differences (idempotence) or diff was missing
    if res_args['check_results'].get('diff', True):
        # do we need to change perms?
        for filename in handler.files_in_archive:
            file_args['path'] = os.path.join(dest, filename)
            try:
                res_args['changed'] = module.set_fs_attributes_if_different(file_args, res_args['changed'])
            except (IOError, OSError), e:
                module.fail_json(msg="Unexpected error when accessing exploded file: %s" % str(e))

    if module.params['list_files']:
        res_args['files'] = handler.files_in_archive

    if res_args['check_results'].get('diff', False):
        res_args['diff'] = { 'prepared' : res_args['check_results']['diff'] }

    module.exit_json(**res_args)

# import module snippets
from ansible.module_utils.basic import *
from ansible.module_utils.urls import *
if __name__ == '__main__':
    main()
