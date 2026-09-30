"""Recover exact pre-module-port bytes for historical vendoring checks.

The module-system/header layers record insertions and before/after hashes.
Separate schemas reverse exact reviewed theta, Hausdorff-instance and adele proof
slices, retaining their statements. These layers do not replace upstream
manifests: callers still check the recovered bytes and replay historical
patches. A hash mismatch is never ignored; arbitrary body edits are unsupported.
"""

import hashlib
import json
from collections import Counter
from pathlib import Path, PurePosixPath
import re

from source_inventory import parse_header, parse_imports


MANIFEST = "third-party/module-system-20260928/manifest.json"
SCHEMA = "unit-distance-module-port-v1"
REPAIR_V1 = "unit-distance-module-port-repair-v1"
REPAIR_V2 = "unit-distance-module-port-repair-v2"
PUBLIC_PROOFS_OPTION = "backward.proofsInPublic true"
PUBLIC_PROOFS_COMMAND = "set_option " + PUBLIC_PROOFS_OPTION + "\n"
PUBLIC_HEADER = "@[expose] public section\nset_option backward.privateInPublic true\n"
PROOF_REPAIR = "unit-distance-module-port-proof-repair-v1"
INSTANCE_PROOF_REPAIR = "unit-distance-module-port-instance-proof-repair-v1"
ADELE_PROOF_REPAIR = "unit-distance-module-port-adele-proof-repair-v1"
PROOF_REPAIR_SCHEMAS = (PROOF_REPAIR, INSTANCE_PROOF_REPAIR, ADELE_PROOF_REPAIR)
THETA_PATH = ("UnitDistance/Upstream/Yamaguchi/ClassFieldTheory/LubinTate/"
              "EqualCharacteristic/Theta/ThetaFirstIdentity.lean")
THETA_DECLARATION = "equalCharacteristicThetaAfterBracketCoefficient_zero"
THETA_STATEMENT = """theorem equalCharacteristicThetaAfterBracketCoefficient_zero
    (u : k⟦X⟧ˣ) :
    equalCharacteristicThetaAfterBracketCoefficient u 0 =
      equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicThetaCoefficient u 0) := by
"""
THETA_PROOF_PREFIX = """  have hsemi := equalCharacteristicPowerSeriesFrobenius_semilinearUnit
    (k := k) (u : k⟦X⟧)
      (by
        intro hzero
        have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
        apply hunit.ne_zero
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero)
  rw [equalCharacteristicThetaCoefficient_zero]
  simpa [equalCharacteristicThetaAfterBracketCoefficient,
    equalCharacteristicQAdditiveCompositionCoefficient,
"""
THETA_BEFORE = ("    equalCharacteristicCompletedSourceBracketCoefficient,\n"
                "    mul_comm] using hsemi.symm\n")
THETA_AFTER = ("    equalCharacteristicCompletedSourceBracketCoefficient] using\n"
               "    (mul_comm _ _).trans hsemi.symm\n")
DIRECT_THETA_PATH = ("UnitDistance/Upstream/Yamaguchi/ClassFieldTheory/LubinTate/"
                     "EqualCharacteristic/CompletedLevel/DirectThetaFirstIdentity.lean")
DIRECT_THETA_DECLARATION = "equalCharacteristicDirectThetaAfterBracketCoefficient_zero"
DIRECT_THETA_STATEMENT = """theorem equalCharacteristicDirectThetaAfterBracketCoefficient_zero
    (u : k⟦X⟧ˣ) :
    equalCharacteristicDirectThetaAfterBracketCoefficient u 0 =
      equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicDirectThetaCoefficient u 0) := by
"""
DIRECT_THETA_PROOF_PREFIX = """  have hsemi := equalCharacteristicPowerSeriesFrobenius_semilinearUnit
    (k := k) (u : k⟦X⟧)
      (by
        intro hzero
        have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
        apply hunit.ne_zero
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero)
  rw [equalCharacteristicDirectThetaCoefficient_zero]
  simpa [equalCharacteristicDirectThetaAfterBracketCoefficient,
    equalCharacteristicQAdditiveCompositionCoefficient,
"""
DIRECT_THETA_BEFORE = ("    equalCharacteristicCompletedDirectBracketCoefficient,\n"
                       "    mul_comm] using hsemi.symm\n")
DIRECT_THETA_AFTER = ("    equalCharacteristicCompletedDirectBracketCoefficient] using\n"
                      "    (mul_comm _ _).trans hsemi.symm\n")
THETA_PROOF_REPAIRS = {
    THETA_PATH: (THETA_DECLARATION, THETA_STATEMENT, THETA_PROOF_PREFIX,
                 THETA_BEFORE, THETA_AFTER),
    DIRECT_THETA_PATH: (DIRECT_THETA_DECLARATION, DIRECT_THETA_STATEMENT,
                        DIRECT_THETA_PROOF_PREFIX, DIRECT_THETA_BEFORE, DIRECT_THETA_AFTER),
}
HAUSDORFF_PATH = ("UnitDistance/Upstream/Yamaguchi/SawinTotallyRealTowers/"
                  "UnramifiedProPRelationRank/Global/MaximalEverywhereUnramifiedProPGalois.lean")
HAUSDORFF_DECLARATION = "MaxEverywhereUnramifiedProPGaloisGroup.instT2Space"
HAUSDORFF_STATEMENT = """instance MaxEverywhereUnramifiedProPGaloisGroup.instT2Space
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    T2Space (MaxEverywhereUnramifiedProPGaloisGroup F p) :="""
HAUSDORFF_CONTEXT = "/-- Hausdorffness inherited from the Krull topology. -/\n"
HAUSDORFF_BEFORE = """
  inferInstanceAs
    (T2Space (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
      maximalEverywhereUnramifiedProP F p))
"""
HAUSDORFF_AFTER = """ by
  change T2Space (maximalEverywhereUnramifiedProP F p ≃ₐ[F]
    maximalEverywhereUnramifiedProP F p)
  exact krullTopology_t2
"""

ADELE_PATH = 'UnitDistance/Upstream/Yamaguchi/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitCore.lean'
ADELE_DECLARATION = 'rationalRelativeAdeleEmbedding_comp'
ADELE_STATEMENT = """theorem rationalRelativeAdeleEmbedding_comp
    {E F H : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F] [NumberField H]
    (hEF : E ≤ F) (hFH : F ≤ H)
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hFH)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hEF) z) =
      RelativeIdeleGroup.adeleEmbedding
        (IntermediateField.inclusion (hEF.trans hFH)) z := by"""
ADELE_CONTEXT = """/-- Scalar extension of relative adeles is transitive in a tower of
intermediate fields. -/
"""
# The repeated old induction body is disambiguated by its unchanged statement.
ADELE_BEFORE = ADELE_STATEMENT + """
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]"""
ADELE_AFTER = ADELE_STATEMENT + """
  exact DFunLike.congr_fun
    (Algebra.TensorProduct.map_id_comp
      (S := NumberField.AdeleRing (𝓞 ℚ) ℚ)
      (A := NumberField.AdeleRing (𝓞 ℚ) ℚ)
      (IntermediateField.inclusion hFH)
      (IntermediateField.inclusion hEF)).symm z"""


MAXIMAL_ABELIAN_PATH = 'UnitDistance/Upstream/Yamaguchi/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MaximalAbelianKernel.lean'
MAXIMAL_ABELIAN_DECLARATION = 'ideleClassComponentQuotientEquivMaximalAbelianGalois'
MAXIMAL_ABELIAN_STATEMENT = """noncomputable def ideleClassComponentQuotientEquivMaximalAbelianGalois :
    ideleClassComponentQuotient K ≃ₜ*
      Gal(maximalAbelianExtension K / K) := by"""
MAXIMAL_ABELIAN_CONTEXT = """/-- Maximal abelian reciprocity identifies the component quotient of the
idele class group with the maximal abelian Galois group. -/
"""
MAXIMAL_ABELIAN_BEFORE = """noncomputable def ideleClassComponentQuotientEquivMaximalAbelianGalois :
    ideleClassComponentQuotient K ≃ₜ*
      Gal(maximalAbelianExtension K / K) := by
  let e : ideleClassComponentQuotient K ≃*
      Gal(maximalAbelianExtension K / K) :=
    QuotientGroup.liftEquiv
      (ideleClassIdentityComponent K)
      (maximalAbelianGlobalArtin_surjective K)
      (maximalAbelianGlobalArtin_ker K).symm
  have heContinuous : Continuous e := by
    apply
      (QuotientGroup.isQuotientMap_mk
        (ideleClassIdentityComponent K)).continuous_iff.mpr
    refine
      (maximalAbelianGlobalArtin K).continuous_toFun.congr
        (fun c => ?_)
    exact
      (QuotientGroup.liftEquiv_coe
        (ideleClassIdentityComponent K)
        (maximalAbelianGlobalArtin_surjective K)
        (maximalAbelianGlobalArtin_ker K).symm c).symm
  let h := heContinuous.homeoOfEquivCompactToT2
  exact
    { toMulEquiv := e
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }"""
MAXIMAL_ABELIAN_LOCAL_INSTANCE = '  letI : T2Space (Gal(maximalAbelianExtension K / K)) := krullTopology_t2\n'
MAXIMAL_ABELIAN_AFTER = MAXIMAL_ABELIAN_BEFORE.replace(
    '  let h := heContinuous.homeoOfEquivCompactToT2\n', MAXIMAL_ABELIAN_LOCAL_INSTANCE +
    '  let h := heContinuous.homeoOfEquivCompactToT2\n')

INSTANCE_PROOF_REPAIRS = {
    HAUSDORFF_PATH: (HAUSDORFF_DECLARATION, HAUSDORFF_STATEMENT,
                     HAUSDORFF_CONTEXT + HAUSDORFF_STATEMENT,
                     HAUSDORFF_BEFORE, HAUSDORFF_AFTER),
    MAXIMAL_ABELIAN_PATH: (MAXIMAL_ABELIAN_DECLARATION, MAXIMAL_ABELIAN_STATEMENT,
                           MAXIMAL_ABELIAN_CONTEXT, MAXIMAL_ABELIAN_BEFORE,
                           MAXIMAL_ABELIAN_AFTER),
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_relative(name):
    if not isinstance(name, str):
        raise ValueError("Module-port source path is not a string")
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or path.as_posix() != name:
        raise ValueError("Unsafe module-port source path: " + name)
    return name


def restore(data, record):
    """Undo recorded text insertions, binding both byte strings by SHA-256."""
    name = record["path"]
    if digest(data) != record["migrated_sha256"]:
        raise ValueError("Module-port current source hash mismatch: " + name)
    text = data.decode("utf-8")
    insertions = record["insertions"]
    shift = sum(len(edit["text"]) for edit in insertions)
    for edit in reversed(insertions):
        shift -= len(edit["text"])
        pos = edit["offset"] + shift
        if text[pos:pos + len(edit["text"])] != edit["text"]:
            raise ValueError("Module-port insertion mismatch: " + name)
        text = text[:pos] + text[pos + len(edit["text"]):]
    original = text.encode("utf-8")
    if any(edit["offset"] > len(text) for edit in insertions):
        raise ValueError("Module-port insertion outside original source: " + name)
    if digest(original) != record["original_sha256"]:
        raise ValueError("Module-port recovered source hash mismatch: " + name)
    return original


def v2_import_directive(text, name):
    """Recognize the recorded single-LF separator without discarding bytes.

    A prefixed record must be exactly one explicit owner import. The raw text
    still participates in insertion reversal and both whole-file hashes.
    """
    if text.startswith("\n"):
        imported, import_only = parse_header("module\n" + text)
        if (not import_only or len(imported) != 1
                or text != "\nimport all " + imported[0] + "\n"):
            raise ValueError("Expected one LF followed by one exact import all directive: " + name)
        return text[1:]
    return text


def validate_v2_insertions(record):
    """Accept only imports and the one documented module compatibility option.

    This schema extends the insertion-only layer, not the kinds of proof edits
    it can conceal. The old schema's stricter unique-import rules are retained.
    Source positions are checked separately when reversing a captured file.
    """
    imports, options = [], []
    for edit in record["insertions"]:
        text = edit["text"]
        if text == PUBLIC_PROOFS_COMMAND:
            options.append(PUBLIC_PROOFS_OPTION)
        else:
            text = v2_import_directive(text, record["path"])
            imported, import_only = parse_header("module\n" + text)
            if (not imported or not import_only or not text.endswith("\n")
                    or not re.match(r"(?:public\s+)?(?:meta\s+)?import\s+", text)):
                raise ValueError("Expected header imports or approved compatibility option: " + record["path"])
            imports.extend(imported)
    if (not record["insertions"] or imports != record.get("added_imports")
            or options != record.get("added_options")
            or len(imports) != len(set(imports)) or len(options) > 1):
        raise ValueError("Repair metadata does not match exact header insertions: " + record["path"])


def validate_v2_positions(previous, current, record):
    """Reject imports in the body and options outside the generated preamble."""
    name = record["path"]
    before, after = previous.decode("utf-8"), current.decode("utf-8")
    old_imports = parse_imports(before)
    for edit in record["insertions"]:
        pos, text = edit["offset"], edit["text"]
        if pos and before[pos - 1:pos] != "\n":
            raise ValueError("Repair insertion is not at a header line boundary: " + name)
        if text == PUBLIC_PROOFS_COMMAND:
            start = pos - len(PUBLIC_HEADER)
            if (start < 0 or before[start:pos] != PUBLIC_HEADER
                    or not parse_header(before[:start])[1]):
                raise ValueError("Compatibility option is not in the generated header: " + name)
        else:
            if not parse_header(before[:pos])[1]:
                raise ValueError("Repair imports were not inserted in the source header: " + name)
            text = v2_import_directive(text, name)
            imported = parse_imports("module\n" + text)
            # A repeated owner is permitted only as an explicit `import all`
            # alongside its existing re-export, never as unexplained duplicates.
            for owner in imported:
                if owner in old_imports and text != "import all " + owner + "\n":
                    raise ValueError("Repeated import owner requires exact import all directive: " + name)
    if Counter(parse_imports(after)) != Counter(old_imports) + Counter(record["added_imports"]):
        raise ValueError("Recorded repair does not explain the import occurrences: " + name)


def validate_theta_repair(record):
    """Permit one exact allowlisted proof slice per layer, not arbitrary edits."""
    change = record.get("replacement", {})
    expected = THETA_PROOF_REPAIRS.get(record["path"])
    if not isinstance(change, dict) or expected is None:
        raise ValueError("Expected the exact reviewed same-statement theta proof repair")
    declaration, statement, _, before, after = expected
    if (record.get("declaration") != declaration
            or record.get("statement") != statement
            or record["insertions"] != [] or record.get("added_imports") != []
            or record.get("added_options") != []
            or set(change) != {"offset", "offset_unit", "before", "after"}
            or change.get("offset_unit") != "utf8-bytes"
            or type(change.get("offset")) is not int or change["offset"] < 0
            or change.get("before") != before or change.get("after") != after):
        raise ValueError("Expected the exact reviewed same-statement theta proof repair")
    return expected


def restore_theta_proof(data, record):
    _, statement_text, prefix_text, before_text, after_text = validate_theta_repair(record)
    return _restore_reviewed_proof(data, record, statement_text,
                                  statement_text + prefix_text, before_text, after_text)


def validate_instance_repair(record):
    """Permit the two exact reviewed Hausdorff-instance proof repairs."""
    change = record.get("replacement", {})
    expected = INSTANCE_PROOF_REPAIRS.get(record["path"])
    if not isinstance(change, dict) or expected is None:
        raise ValueError("Expected the exact reviewed same-statement instance proof repair")
    declaration, statement, _, before, after = expected
    if (record.get("declaration") != declaration
            or record.get("statement") != statement
            or record["insertions"] != [] or record.get("added_imports") != []
            or record.get("added_options") != []
            or set(change) != {"offset", "offset_unit", "before", "after"}
            or change.get("offset_unit") != "utf8-bytes"
            or type(change.get("offset")) is not int or change["offset"] < 0
            or change.get("before") != before
            or change.get("after") != after):
        raise ValueError("Expected the exact reviewed same-statement instance proof repair")
    return expected


def restore_instance_proof(data, record):
    _, statement, context, before, after = validate_instance_repair(record)
    return _restore_reviewed_proof(data, record, statement, context, before, after)


def validate_adele_repair(record):
    """Permit only the reviewed adele-composition theorem proof, with the same type."""
    change = record.get("replacement", {})
    if not isinstance(change, dict):
        raise ValueError("Expected the exact reviewed same-statement adele proof repair")
    if (record["path"] != ADELE_PATH
            or record.get("declaration") != ADELE_DECLARATION
            or record.get("statement") != ADELE_STATEMENT
            or record["insertions"] != [] or record.get("added_imports") != []
            or record.get("added_options") != []
            or set(change) != {"offset", "offset_unit", "before", "after"}
            or change.get("offset_unit") != "utf8-bytes"
            or type(change.get("offset")) is not int or change["offset"] < 0
            or change.get("before") != ADELE_BEFORE
            or change.get("after") != ADELE_AFTER):
        raise ValueError("Expected the exact reviewed same-statement adele proof repair")


def restore_adele_proof(data, record):
    validate_adele_repair(record)
    return _restore_reviewed_proof(data, record, ADELE_STATEMENT,
                                  ADELE_CONTEXT, ADELE_BEFORE, ADELE_AFTER)


def _restore_reviewed_proof(data, record, statement_text, prefix_text, before_text, after_text):
    """Reverse constants supplied by the strict validators, never record text."""
    if digest(data) != record["migrated_sha256"]:
        raise ValueError("Module-port current source hash mismatch: " + record["path"])
    before, after = before_text.encode(), after_text.encode()
    statement = statement_text.encode()
    prefix = prefix_text.encode()
    offset = record["replacement"]["offset"]
    # The exact statement and preceding proof context identify this proof,
    # independently of the record's claimed location and whole-file hashes.
    if (data.count(statement) != 1 or data.count(after) != 1
            or data.count(prefix + after) != 1
            or offset != data.index(prefix + after) + len(prefix)
            or data[offset:offset + len(after)] != after):
        raise ValueError("Reviewed proof repair has nonunique or wrong declaration context")
    original = data[:offset] + before + data[offset + len(after):]
    if original.count(before) != 1:
        raise ValueError("Reviewed proof repair has multiple original proof matches")
    if digest(original) != record["original_sha256"]:
        raise ValueError("Module-port recovered source hash mismatch: " + record["path"])
    return original


class ModulePort:
    def __init__(self, root):
        self.root = Path(root)
        self.records = {}
        self.used_paths = set()
        self.manifest_sha256 = None
        self.repair_layers = []
        path = self.root / MANIFEST
        if not path.exists() and not path.is_symlink():
            if list(path.parent.glob("repairs-*.json")):
                raise ValueError("Module-port repair layer has no base manifest")
            return  # Historical snapshots predate this additional layer.
        if path.is_symlink() or not path.is_file():
            raise ValueError("Module-port manifest is not a regular file")
        data = path.read_bytes()
        manifest = json.loads(data)
        if manifest.get("schema") != SCHEMA or manifest.get("applied") is not True:
            raise ValueError("Expected an applied module-port-v1 manifest")
        self.records = self.validate_records(manifest)
        self.manifest_sha256 = digest(data)
        expected_hashes = {name: record["migrated_sha256"] for name, record in self.records.items()}
        for repair_path in sorted(path.parent.glob("repairs-*.json")):
            if repair_path.is_symlink() or not repair_path.is_file():
                raise ValueError("Module-port repair is not a regular file")
            repair_data = repair_path.read_bytes()
            repair = json.loads(repair_data)
            schema = repair.get("schema")
            if (schema not in (REPAIR_V1, REPAIR_V2, *PROOF_REPAIR_SCHEMAS)
                    or repair.get("applied") is not True
                    or repair.get("base_manifest") != MANIFEST
                    or repair.get("base_manifest_sha256") != self.manifest_sha256):
                raise ValueError("Module-port repair does not bind the applied base manifest")
            records = self.validate_records(repair)
            if schema in PROOF_REPAIR_SCHEMAS and len(records) != 1:
                raise ValueError("Reviewed proof repair must contain exactly one file")
            for name, record in records.items():
                if record["original_sha256"] != expected_hashes.get(name):
                    raise ValueError("Broken module-port repair hash chain: " + name)
                if schema == REPAIR_V1:
                    imported, import_only = parse_header("module\n" + "".join(
                        edit["text"] for edit in record["insertions"]))
                    if (not imported or not import_only
                            or imported != record.get("added_imports")
                            or len(imported) != len(set(imported))):
                        raise ValueError("Expected exact header-import repair insertions: " + name)
                elif schema == REPAIR_V2:
                    validate_v2_insertions(record)
                elif schema == PROOF_REPAIR:
                    validate_theta_repair(record)
                elif schema == INSTANCE_PROOF_REPAIR:
                    validate_instance_repair(record)
                else:
                    validate_adele_repair(record)
                expected_hashes[name] = record["migrated_sha256"]
            self.repair_layers.append({
                "manifest": repair_path.relative_to(self.root).as_posix(),
                "manifest_sha256": digest(repair_data), "schema": schema,
                "records": records, "used_paths": set(),
            })

    @staticmethod
    def validate_records(manifest):
        if not isinstance(manifest.get("files"), list):
            raise ValueError("Module-port manifest lacks a file list")
        records = {}
        for record in manifest["files"]:
            name = safe_relative(record.get("path"))
            if name in records:
                raise ValueError("Duplicate module-port source path: " + name)
            for key in ("original_sha256", "migrated_sha256"):
                if not re.fullmatch(r"[0-9a-f]{64}", record.get(key, "")):
                    raise ValueError("Invalid module-port source hash: " + name)
            edits = record.get("insertions")
            if not isinstance(edits, list):
                raise ValueError("Module-port insertions are not a list: " + name)
            previous = -1
            for edit in edits:
                offset = edit.get("offset")
                if (type(offset) is not int or offset < previous or offset < 0
                        or not isinstance(edit.get("text"), str) or not edit["text"]):
                    raise ValueError("Invalid module-port insertion: " + name)
                previous = offset
            records[name] = record
        return records

    def read(self, name):
        name = safe_relative(name)
        path = self.root / name
        if path.is_symlink() or not path.is_file():
            raise ValueError("Expected regular provenance source: " + name)
        data = path.read_bytes()
        return self.recover(name, data)

    def recover(self, name, data):
        """Recover baseline bytes from an already captured regular source."""
        name = safe_relative(name)
        for layer in reversed(self.repair_layers):
            if name in layer["records"]:
                record = layer["records"][name]
                if layer["schema"] == PROOF_REPAIR:
                    previous = restore_theta_proof(data, record)
                elif layer["schema"] == INSTANCE_PROOF_REPAIR:
                    previous = restore_instance_proof(data, record)
                elif layer["schema"] == ADELE_PROOF_REPAIR:
                    previous = restore_adele_proof(data, record)
                else:
                    previous = restore(data, record)
                if layer["schema"] == REPAIR_V1:
                    before = parse_imports(previous.decode("utf-8"))
                    after = parse_imports(data.decode("utf-8"))
                    added = record["added_imports"]
                    if (set(added) & set(before)
                            or [item for item in after if item not in added] != before
                            or [item for item in after if item in added] != added):
                        raise ValueError("Repair imports were not inserted in the source header: " + name)
                elif layer["schema"] == REPAIR_V2:
                    validate_v2_positions(previous, data, record)
                layer["used_paths"].add(name)
                data = previous
        if name in self.records:
            self.used_paths.add(name)
            return restore(data, self.records[name])
        return data

    def evidence(self):
        return {"manifest": MANIFEST if self.manifest_sha256 else None,
                "manifest_sha256": self.manifest_sha256,
                "checked_files": len(self.used_paths),
                "reversed_files": sum(bool(self.records[name]["insertions"])
                                      for name in self.used_paths),
                "repair_layers": [{"manifest": layer["manifest"],
                                   "schema": layer["schema"],
                                   "manifest_sha256": layer["manifest_sha256"],
                                   "checked_files": len(layer["used_paths"])}
                                  for layer in self.repair_layers]}
