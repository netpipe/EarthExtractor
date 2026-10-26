#include <QCoreApplication>
#include <QNetworkAccessManager>
#include <QNetworkReply>
#include <QNetworkRequest>
#include <QUrl>
#include <QUrlQuery>
#include <QJsonDocument>
#include <QJsonObject>
#include <QJsonArray>
#include <QJsonValue>
#include <QFile>
#include <QDir>
#include <QEventLoop>
#include <QTimer>
#include <QDebug>
#include <QSet>
#include <QMap>
#include <QTextStream>
#include <QtEndian>
#include <QStringList>
#include <QByteArray>
#include <QVector>

#include <cmath>
#include <cstring>
#include <cstdint>

static const double kPi = 3.14159265358979323846;

static double deg2rad(double d)
{
    return d * kPi / 180.0;
}

// ---------------------------------------------------------------------------
// Simple blocking HTTP fetcher for Qt 5.12 console app.
// ---------------------------------------------------------------------------
class Fetcher
{
public:
    QByteArray get(const QUrl& url)
    {
        QNetworkRequest req(url);
        req.setHeader(QNetworkRequest::UserAgentHeader,
                      QStringLiteral("Qt512-3DTiles2OBJ/1.0"));

        // Follow safe redirects.
        req.setAttribute(QNetworkRequest::RedirectPolicyAttribute,
                         QNetworkRequest::NoLessSafeRedirectPolicy);

        QNetworkReply* reply = m_nam.get(req);

        QEventLoop loop;
        QObject::connect(reply, &QNetworkReply::finished,
                         &loop, &QEventLoop::quit);

        QTimer timer;
        timer.setSingleShot(true);
        QObject::connect(&timer, &QTimer::timeout,
                         &loop, &QEventLoop::quit);
        timer.start(90000); // 90 seconds per request.

        loop.exec();

        if (!reply->isFinished()) {
            reply->abort();
            reply->deleteLater();
            qWarning() << "Timeout:" << url;
            return QByteArray();
        }

        int status = reply->attribute(QNetworkRequest::HttpStatusCodeAttribute).toInt();
        QByteArray data = reply->readAll();
        QNetworkReply::NetworkError err = reply->error();
        QString errString = reply->errorString();
        reply->deleteLater();

        if (err != QNetworkReply::NoError) {
            qWarning() << "Network error:" << url << errString;
            return QByteArray();
        }

        if (status != 0 && status != 200) {
            qWarning() << "HTTP error" << status << url;
            return QByteArray();
        }

        return data;
    }

private:
    QNetworkAccessManager m_nam;
};

// ---------------------------------------------------------------------------
// URL helpers.
// ---------------------------------------------------------------------------
static QUrl ensureKey(const QUrl& url, const QString& apiKey)
{
    if (apiKey.isEmpty())
        return url;

    QUrl u = url;
    QUrlQuery q(u);

    if (!q.hasQueryItem("key"))
        q.addQueryItem("key", apiKey);

    u.setQuery(q);
    return u;
}

static QUrl resolveUrl(const QUrl& base, const QString& uri)
{
    if (uri.isEmpty())
        return base;

    QUrl u(uri);
    if (u.isRelative())
        u = base.resolved(u);

    return u;
}

// ---------------------------------------------------------------------------
// Geographic helpers.
// ---------------------------------------------------------------------------
struct Vec3
{
    double x = 0.0;
    double y = 0.0;
    double z = 0.0;
};

static Vec3 geodeticToEcef(double latRad, double lonRad, double h = 0.0)
{
    const double a = 6378137.0;
    const double f = 1.0 / 298.257223563;
    const double e2 = f * (2.0 - f);

    double sinLat = std::sin(latRad);
    double cosLat = std::cos(latRad);
    double sinLon = std::sin(lonRad);
    double cosLon = std::cos(lonRad);

    double N = a / std::sqrt(1.0 - e2 * sinLat * sinLat);

    Vec3 p;
    p.x = (N + h) * cosLat * cosLon;
    p.y = (N + h) * cosLat * sinLon;
    p.z = ((1.0 - e2) * N + h) * sinLat;

    return p;
}

static bool pointInRegion(const QJsonArray& region, double latRad, double lonRad)
{
    // 3D Tiles region:
    // [west, south, east, north, minHeight, maxHeight] in radians/meters.
    if (region.size() < 4)
        return true;

    double west  = region[0].toDouble();
    double south = region[1].toDouble();
    double east  = region[2].toDouble();
    double north = region[3].toDouble();

    bool lonOk = false;
    if (west <= east)
        lonOk = (lonRad >= west && lonRad <= east);
    else
        lonOk = (lonRad >= west || lonRad <= east); // antimeridian crossing

    bool latOk = (latRad >= south && latRad <= north);

    return lonOk && latOk;
}

static double detCols(double ax, double ay, double az,
                      double bx, double by, double bz,
                      double cx, double cy, double cz)
{
    // Determinant of matrix with columns A, B, C.
    return ax * (by * cz - bz * cy)
         - ay * (bx * cz - bz * cx)
         + az * (bx * cy - by * cx);
}

static bool pointInBoundingVolume(const QJsonObject& bv,
                                  double latRad,
                                  double lonRad)
{
    if (bv.isEmpty())
        return true;

    if (bv.contains("region")) {
        return pointInRegion(bv.value("region").toArray(), latRad, lonRad);
    }

    Vec3 p = geodeticToEcef(latRad, lonRad, 0.0);

    if (bv.contains("box")) {
        QJsonArray b = bv.value("box").toArray();

        // 3D Tiles box:
        // center.x center.y center.z
        // xAxis.x xAxis.y xAxis.z
        // yAxis.x yAxis.y yAxis.z
        // zAxis.x zAxis.y zAxis.z
        if (b.size() >= 12) {
            double cx = b[0].toDouble();
            double cy = b[1].toDouble();
            double cz = b[2].toDouble();

            double Xx = b[3].toDouble();
            double Xy = b[4].toDouble();
            double Xz = b[5].toDouble();

            double Yx = b[6].toDouble();
            double Yy = b[7].toDouble();
            double Yz = b[8].toDouble();

            double Zx = b[9].toDouble();
            double Zy = b[10].toDouble();
            double Zz = b[11].toDouble();

            double px = p.x - cx;
            double py = p.y - cy;
            double pz = p.z - cz;

            double det = detCols(Xx, Xy, Xz,
                                 Yx, Yy, Yz,
                                 Zx, Zy, Zz);

            if (std::fabs(det) < 1e-12)
                return true;

            double u = detCols(px, py, pz,
                               Yx, Yy, Yz,
                               Zx, Zy, Zz) / det;

            double v = detCols(Xx, Xy, Xz,
                               px, py, pz,
                               Zx, Zy, Zz) / det;

            double w = detCols(Xx, Xy, Xz,
                               Yx, Yy, Yz,
                               px, py, pz) / det;

            const double eps = 1.000001;
            return std::fabs(u) <= eps &&
                   std::fabs(v) <= eps &&
                   std::fabs(w) <= eps;
        }
    }

    if (bv.contains("sphere")) {
        QJsonArray s = bv.value("sphere").toArray();
        if (s.size() >= 4) {
            double cx = s[0].toDouble();
            double cy = s[1].toDouble();
            double cz = s[2].toDouble();
            double r  = s[3].toDouble();

            double dx = p.x - cx;
            double dy = p.y - cy;
            double dz = p.z - cz;

            double rr = r + 1.0;
            return (dx * dx + dy * dy + dz * dz) <= rr * rr;
        }
    }

    // Unknown/extension bounding volume: do not cull.
    // This may download more tiles than necessary.
    return true;
}

// ---------------------------------------------------------------------------
// OBJ/MTL writer state.
// ---------------------------------------------------------------------------
class ObjWriter
{
public:
    QString outDir;
    QString texDir;
    QString objPath;
    QString mtlPath;

    QFile objFile;
    QTextStream obj;

    // OBJ indices are 1-based.
    int vOffset  = 1;
    int vtOffset = 1;
    int vnOffset = 1;

    QMap<QString, QString> mtlDefs;

    bool open(const QString& dir)
    {
        outDir  = dir;
        texDir  = outDir + QStringLiteral("/textures");
        objPath = outDir + QStringLiteral("/scene.obj");
        mtlPath = outDir + QStringLiteral("/scene.mtl");

        if (!QDir().mkpath(outDir))
            return false;

        if (!QDir().mkpath(texDir))
            return false;

        objFile.setFileName(objPath);
        if (!objFile.open(QIODevice::WriteOnly | QIODevice::Text))
            return false;

        obj.setDevice(&objFile);
        obj.setRealNumberPrecision(9);

        obj << "# Exported from Google Photorealistic 3D Tiles starter tool\n";
        obj << "# Check Google Maps Platform terms before using exported data.\n";
        obj << "mtllib scene.mtl\n";

        return true;
    }

    void close()
    {
        obj.flush();

        if (objFile.isOpen())
            objFile.close();

        QFile mtl(mtlPath);
        if (!mtl.open(QIODevice::WriteOnly | QIODevice::Text))
            return;

        QTextStream out(&mtl);
        out << "# Materials generated by Qt 5.12 3D Tiles OBJ starter\n";

        for (auto it = mtlDefs.constBegin(); it != mtlDefs.constEnd(); ++it) {
            out << it.value() << "\n";
        }

        out.flush();
        mtl.close();
    }
};

// ---------------------------------------------------------------------------
// Minimal glTF-Binary parser.
// ---------------------------------------------------------------------------
struct GltfData
{
    QJsonObject json;
    QByteArray bin;
};

static bool parseGlb(const QByteArray& data, GltfData& out)
{
    if (data.size() < 12)
        return false;

    if (data.mid(0, 4) != QByteArrayLiteral("glTF"))
        return false;

    const uchar* p = reinterpret_cast<const uchar*>(data.constData());

    quint32 version = qFromLittleEndian<quint32>(p + 4);
    if (version != 2)
        return false;

    int pos = 12;

    while (pos + 8 <= data.size()) {
        quint32 chunkLength = qFromLittleEndian<quint32>(p + pos);
        quint32 chunkType   = qFromLittleEndian<quint32>(p + pos + 4);

        int start = pos + 8;
        if (start + int(chunkLength) > data.size())
            break;

        // JSON chunk: "JSON"
        if (chunkType == 0x4E4F534Au) {
            QJsonParseError err;
            QJsonDocument doc = QJsonDocument::fromJson(
                data.mid(start, int(chunkLength)), &err);

            if (err.error == QJsonParseError::NoError && doc.isObject())
                out.json = doc.object();
        }
        // BIN chunk: "BIN\0"
        else if (chunkType == 0x004E4942u) {
            out.bin = data.mid(start, int(chunkLength));
        }

        quint32 padded = (chunkLength + 3u) & ~quint32(3u);
        if (padded == 0)
            break;

        pos = start + int(padded);
    }

    return !out.json.isEmpty();
}

static QByteArray bufferViewData(const GltfData& gltf, int bufferViewIndex)
{
    QJsonArray bufferViews = gltf.json.value("bufferViews").toArray();

    if (bufferViewIndex < 0 || bufferViewIndex >= bufferViews.size())
        return QByteArray();

    QJsonObject bv = bufferViews.at(bufferViewIndex).toObject();

    int bufferIndex = bv.value("buffer").toInt(0);
    if (bufferIndex != 0) {
        // This starter only supports buffer 0, which is normal for GLB.
        return QByteArray();
    }

    int byteOffset = bv.value("byteOffset").toInt(0);
    int byteLength = bv.value("byteLength").toInt(0);

    if (byteOffset < 0 || byteLength < 0)
        return QByteArray();

    if (byteOffset + byteLength > gltf.bin.size())
        return QByteArray();

    return gltf.bin.mid(byteOffset, byteLength);
}

static int componentSize(int componentType)
{
    switch (componentType) {
    case 5120: // BYTE
    case 5121: // UNSIGNED_BYTE
        return 1;
    case 5122: // SHORT
    case 5123: // UNSIGNED_SHORT
        return 2;
    case 5125: // UNSIGNED_INT
    case 5126: // FLOAT
        return 4;
    default:
        return 0;
    }
}

static int typeComponentCount(const QString& type)
{
    if (type == QLatin1String("SCALAR")) return 1;
    if (type == QLatin1String("VEC2"))    return 2;
    if (type == QLatin1String("VEC3"))    return 3;
    if (type == QLatin1String("VEC4"))    return 4;
    if (type == QLatin1String("MAT2"))    return 4;
    if (type == QLatin1String("MAT3"))    return 9;
    if (type == QLatin1String("MAT4"))    return 16;
    return 0;
}

static float readFloatComponent(const QByteArray& view,
                                int offset,
                                int componentType,
                                bool normalized)
{
    int sz = componentSize(componentType);
    if (offset < 0 || offset + sz > view.size())
        return 0.0f;

    const uchar* p = reinterpret_cast<const uchar*>(view.constData()) + offset;

    switch (componentType) {
    case 5126: { // FLOAT
        float f = 0.0f;
        std::memcpy(&f, p, sizeof(float));
        return f;
    }

    case 5120: { // BYTE
        qint8 v = static_cast<qint8>(*p);
        if (normalized)
            return qMax<float>(float(v) / 127.0f, -1.0f);
        return float(v);
    }

    case 5121: { // UNSIGNED_BYTE
        quint8 v = *p;
        if (normalized)
            return float(v) / 255.0f;
        return float(v);
    }

    case 5122: { // SHORT
        qint16 v = qFromLittleEndian<qint16>(p);
        if (normalized)
            return qMax<float>(float(v) / 32767.0f, -1.0f);
        return float(v);
    }

    case 5123: { // UNSIGNED_SHORT
        quint16 v = qFromLittleEndian<quint16>(p);
        if (normalized)
            return float(v) / 65535.0f;
        return float(v);
    }

    case 5125: { // UNSIGNED_INT
        quint32 v = qFromLittleEndian<quint32>(p);
        if (normalized)
            return float(v) / 4294967295.0f;
        return float(v);
    }

    default:
        return 0.0f;
    }
}

static QVector<float> readFloatAccessor(const GltfData& gltf, int accessorIndex)
{
    QVector<float> out;

    QJsonArray accessors = gltf.json.value("accessors").toArray();
    if (accessorIndex < 0 || accessorIndex >= accessors.size())
        return out;

    QJsonObject acc = accessors.at(accessorIndex).toObject();

    int bufferViewIndex = acc.value("bufferView").toInt(-1);
    if (bufferViewIndex < 0)
        return out;

    QJsonArray bufferViews = gltf.json.value("bufferViews").toArray();
    if (bufferViewIndex >= bufferViews.size())
        return out;

    QJsonObject bv = bufferViews.at(bufferViewIndex).toObject();
    QByteArray view = bufferViewData(gltf, bufferViewIndex);
    if (view.isEmpty())
        return out;

    int byteOffset    = acc.value("byteOffset").toInt(0);
    int componentType = acc.value("componentType").toInt(0);
    int count         = acc.value("count").toInt(0);
    QString type      = acc.value("type").toString();
    bool normalized   = acc.value("normalized").toBool(false);

    int components = typeComponentCount(type);
    int compSize   = componentSize(componentType);

    if (components <= 0 || compSize <= 0 || count <= 0)
        return out;

    int stride = bv.value("byteStride").toInt(0);
    if (stride <= 0)
        stride = components * compSize;

    out.reserve(count * components);

    for (int i = 0; i < count; ++i) {
        int base = byteOffset + i * stride;

        for (int c = 0; c < components; ++c) {
            int off = base + c * compSize;
            out.append(readFloatComponent(view, off, componentType, normalized));
        }
    }

    return out;
}

static QVector<quint32> readIndexAccessor(const GltfData& gltf, int accessorIndex)
{
    QVector<quint32> out;

    QJsonArray accessors = gltf.json.value("accessors").toArray();
    if (accessorIndex < 0 || accessorIndex >= accessors.size())
        return out;

    QJsonObject acc = accessors.at(accessorIndex).toObject();

    if (acc.value("type").toString() != QLatin1String("SCALAR"))
        return out;

    int bufferViewIndex = acc.value("bufferView").toInt(-1);
    if (bufferViewIndex < 0)
        return out;

    QJsonArray bufferViews = gltf.json.value("bufferViews").toArray();
    if (bufferViewIndex >= bufferViews.size())
        return out;

    QJsonObject bv = bufferViews.at(bufferViewIndex).toObject();
    QByteArray view = bufferViewData(gltf, bufferViewIndex);
    if (view.isEmpty())
        return out;

    int byteOffset    = acc.value("byteOffset").toInt(0);
    int componentType = acc.value("componentType").toInt(0);
    int count         = acc.value("count").toInt(0);

    int compSize = componentSize(componentType);
    if (compSize <= 0 || count <= 0)
        return out;

    int stride = bv.value("byteStride").toInt(0);
    if (stride <= 0)
        stride = compSize;

    out.reserve(count);

    for (int i = 0; i < count; ++i) {
        int off = byteOffset + i * stride;

        if (off < 0 || off + compSize > view.size())
            continue;

        const uchar* p = reinterpret_cast<const uchar*>(view.constData()) + off;

        switch (componentType) {
        case 5121: // UNSIGNED_BYTE
            out.append(quint32(*p));
            break;

        case 5123: // UNSIGNED_SHORT
            out.append(quint32(qFromLittleEndian<quint16>(p)));
            break;

        case 5125: // UNSIGNED_INT
            out.append(qFromLittleEndian<quint32>(p));
            break;

        case 5122: { // SHORT, rare for indices; accept non-negative values.
            qint16 v = qFromLittleEndian<qint16>(p);
            if (v >= 0)
                out.append(quint32(v));
            break;
        }

        default:
            break;
        }
    }

    return out;
}

// ---------------------------------------------------------------------------
// Texture extraction.
// ---------------------------------------------------------------------------
static QString mimeTypeToExtension(const QString& mime)
{
    QString m = mime.toLower();

    if (m.contains(QLatin1String("png")))
        return QStringLiteral("png");

    if (m.contains(QLatin1String("jpeg")) || m.contains(QLatin1String("jpg")))
        return QStringLiteral("jpg");

    if (m.contains(QLatin1String("webp")))
        return QStringLiteral("webp");

    if (m.contains(QLatin1String("gif")))
        return QStringLiteral("gif");

    return QStringLiteral("bin");
}

static QString saveImage(const GltfData& gltf,
                         int imageIndex,
                         const QString& baseName,
                         const QString& texDir,
                         QMap<int, QString>& cache)
{
    if (imageIndex < 0)
        return QString();

    if (cache.contains(imageIndex))
        return cache.value(imageIndex);

    QJsonArray images = gltf.json.value("images").toArray();
    if (imageIndex >= images.size())
        return QString();

    QJsonObject image = images.at(imageIndex).toObject();

    QByteArray bytes;
    QString mime;

    if (image.contains("bufferView")) {
        bytes = bufferViewData(gltf, image.value("bufferView").toInt(-1));
        mime  = image.value("mimeType").toString();
    } else if (image.contains("uri")) {
        QString uri = image.value("uri").toString();

        if (uri.startsWith(QLatin1String("data:"))) {
            int comma = uri.indexOf(QLatin1Char(','));
            if (comma > 0) {
                QString header  = uri.left(comma);
                QString payload = uri.mid(comma + 1);

                int semi = header.indexOf(QLatin1Char(';'));
                mime = header.mid(5, semi - 5); // skip "data:"

                bytes = QByteArray::fromBase64(payload.toUtf8());
            }
        } else {
            // External image URIs are not downloaded by this starter.
            return QString();
        }
    }

    if (bytes.isEmpty())
        return QString();

    QString ext = mimeTypeToExtension(mime);

    if (ext == QLatin1String("bin")) {
        if (bytes.size() > 3 &&
            static_cast<uchar>(bytes.at(0)) == 0x89 &&
            bytes.mid(1, 3) == "PNG") {
            ext = QStringLiteral("png");
        } else if (bytes.size() > 2 &&
                   static_cast<uchar>(bytes.at(0)) == 0xFF &&
                   static_cast<uchar>(bytes.at(1)) == 0xD8) {
            ext = QStringLiteral("jpg");
        }
    }

    if (!QDir().mkpath(texDir))
        return QString();

    QString fileName = baseName +
                       QStringLiteral("_img") +
                       QString::number(imageIndex) +
                       QStringLiteral(".") + ext;

    QString fullPath = texDir + QStringLiteral("/") + fileName;

    QFile f(fullPath);
    if (!f.open(QIODevice::WriteOnly))
        return QString();

    f.write(bytes);
    f.close();

    QString rel = QStringLiteral("textures/") + fileName;
    cache.insert(imageIndex, rel);

    return rel;
}

static QString ensureMaterial(const GltfData& gltf,
                              int materialIndex,
                              int tileId,
                              ObjWriter& writer,
                              QMap<int, QString>& imageCache,
                              const QString& texBaseName)
{
    QString name;

    if (materialIndex < 0)
        name = QStringLiteral("tile%1_default").arg(tileId);
    else
        name = QStringLiteral("tile%1_mat%2").arg(tileId).arg(materialIndex);

    if (writer.mtlDefs.contains(name))
        return name;

    QString textureFile;

    QJsonArray materials = gltf.json.value("materials").toArray();

    if (materialIndex >= 0 && materialIndex < materials.size()) {
        QJsonObject material = materials.at(materialIndex).toObject();
        QJsonObject pbr = material.value("pbrMetallicRoughness").toObject();

        if (pbr.contains("baseColorTexture")) {
            QJsonObject baseColorTexture = pbr.value("baseColorTexture").toObject();
            int textureIndex = baseColorTexture.value("index").toInt(-1);

            QJsonArray textures = gltf.json.value("textures").toArray();

            if (textureIndex >= 0 && textureIndex < textures.size()) {
                QJsonObject texture = textures.at(textureIndex).toObject();
                int imageIndex = texture.value("source").toInt(-1);

                textureFile = saveImage(gltf,
                                        imageIndex,
                                        texBaseName,
                                        writer.texDir,
                                        imageCache);
            }
        }
    }

    QStringList mtl;
    mtl << QStringLiteral("newmtl ") + name;

    if (!textureFile.isEmpty()) {
        mtl << QStringLiteral("map_Kd ") + textureFile;
    } else {
        mtl << QStringLiteral("Kd 1.000 1.000 1.000");
    }

    mtl << QStringLiteral("illum 1");

    writer.mtlDefs.insert(name, mtl.join(QStringLiteral("\n")));

    return name;
}

// ---------------------------------------------------------------------------
// glTF primitive -> OBJ.
// ---------------------------------------------------------------------------
static bool writePrimitive(const GltfData& gltf,
                           const QJsonObject& primitive,
                           int primitiveIndex,
                           int tileId,
                           ObjWriter& writer,
                           QMap<int, QString>& imageCache)
{
    // glTF mode 4 = TRIANGLES.
    int mode = primitive.value("mode").toInt(4);
    if (mode != 4)
        return false;

    QJsonObject attributes = primitive.value("attributes").toObject();

    int positionAccessor = attributes.value("POSITION").toInt(-1);
    if (positionAccessor < 0)
        return false;

    QVector<float> positions = readFloatAccessor(gltf, positionAccessor);
    if (positions.size() < 3)
        return false;

    int vertexCount = positions.size() / 3;

    QVector<float> normals;
    if (attributes.contains("NORMAL")) {
        normals = readFloatAccessor(gltf, attributes.value("NORMAL").toInt(-1));
        if (normals.size() != vertexCount * 3)
            normals.clear();
    }

    QVector<float> uvs;
    if (attributes.contains("TEXCOORD_0")) {
        uvs = readFloatAccessor(gltf, attributes.value("TEXCOORD_0").toInt(-1));
        if (uvs.size() != vertexCount * 2)
            uvs.clear();
    }

    // glTF UV origin is top-left; OBJ UV origin is bottom-left.
    for (int i = 0; i < uvs.size() / 2; ++i) {
        uvs[2 * i + 1] = 1.0f - uvs[2 * i + 1];
    }

    int materialIndex = primitive.value("material").toInt(-1);
    QString texBaseName = QStringLiteral("tile%1").arg(tileId);

    QString materialName = ensureMaterial(gltf,
                                          materialIndex,
                                          tileId,
                                          writer,
                                          imageCache,
                                          texBaseName);

    writer.obj << "g tile" << tileId << "_p" << primitiveIndex << "\n";
    writer.obj << "usemtl " << materialName << "\n";

    int vBase  = writer.vOffset;
    int vtBase = writer.vtOffset;
    int vnBase = writer.vnOffset;

    // Write vertices.
    for (int i = 0; i < vertexCount; ++i) {
        writer.obj << "v "
                   << positions[3 * i + 0] << ' '
                   << positions[3 * i + 1] << ' '
                   << positions[3 * i + 2] << "\n";
        ++writer.vOffset;
    }

    // Write UVs.
    if (!uvs.isEmpty()) {
        for (int i = 0; i < vertexCount; ++i) {
            writer.obj << "vt "
                       << uvs[2 * i + 0] << ' '
                       << uvs[2 * i + 1] << "\n";
            ++writer.vtOffset;
        }
    }

    // Write normals.
    if (!normals.isEmpty()) {
        for (int i = 0; i < vertexCount; ++i) {
            writer.obj << "vn "
                       << normals[3 * i + 0] << ' '
                       << normals[3 * i + 1] << ' '
                       << normals[3 * i + 2] << "\n";
            ++writer.vnOffset;
        }
    }

    QVector<quint32> indices;

    if (primitive.contains("indices")) {
        indices = readIndexAccessor(gltf, primitive.value("indices").toInt(-1));
        if (indices.isEmpty())
            return false;
    } else {
        indices.reserve(vertexCount);
        for (int i = 0; i < vertexCount; ++i)
            indices.append(quint32(i));
    }

    // Write faces.
    for (int i = 0; i + 2 < indices.size(); i += 3) {
        quint32 a = indices[i + 0];
        quint32 b = indices[i + 1];
        quint32 c = indices[i + 2];

        if (a >= quint32(vertexCount) ||
            b >= quint32(vertexCount) ||
            c >= quint32(vertexCount)) {
            continue;
        }

        int va = vBase + int(a);
        int vb = vBase + int(b);
        int vc = vBase + int(c);

        if (!uvs.isEmpty() && !normals.isEmpty()) {
            int vta = vtBase + int(a);
            int vtb = vtBase + int(b);
            int vtc = vtBase + int(c);

            int vna = vnBase + int(a);
            int vnb = vnBase + int(b);
            int vnc = vnBase + int(c);

            writer.obj << "f "
                       << va << '/' << vta << '/' << vna << ' '
                       << vb << '/' << vtb << '/' << vnb << ' '
                       << vc << '/' << vtc << '/' << vnc;
        } else if (!uvs.isEmpty()) {
            int vta = vtBase + int(a);
            int vtb = vtBase + int(b);
            int vtc = vtBase + int(c);

            writer.obj << "f "
                       << va << '/' << vta << ' '
                       << vb << '/' << vtb << ' '
                       << vc << '/' << vtc;
        } else if (!normals.isEmpty()) {
            int vna = vnBase + int(a);
            int vnb = vnBase + int(b);
            int vnc = vnBase + int(c);

            writer.obj << "f "
                       << va << "//" << vna << ' '
                       << vb << "//" << vnb << ' '
                       << vc << "//" << vnc;
        } else {
            writer.obj << "f "
                       << va << ' '
                       << vb << ' '
                       << vc;
        }

        writer.obj << "\n";
    }

    return true;
}

static bool exportGlb(const QByteArray& glbBytes,
                      int tileId,
                      ObjWriter& writer)
{
    GltfData gltf;
    if (!parseGlb(glbBytes, gltf))
        return false;

    QMap<int, QString> imageCache;

    bool wrote = false;

    QJsonArray meshes = gltf.json.value("meshes").toArray();

    for (int m = 0; m < meshes.size(); ++m) {
        QJsonObject mesh = meshes.at(m).toObject();
        QJsonArray primitives = mesh.value("primitives").toArray();

        for (int p = 0; p < primitives.size(); ++p) {
            QJsonObject primitive = primitives.at(p).toObject();

            if (writePrimitive(gltf, primitive, p, tileId, writer, imageCache))
                wrote = true;
        }
    }

    return wrote;
}

// ---------------------------------------------------------------------------
// 3D Tiles traversal.
// ---------------------------------------------------------------------------
struct ExportContext
{
    Fetcher* fetcher = nullptr;
    ObjWriter* writer = nullptr;

    QString apiKey;

    double latRad = 0.0;
    double lonRad = 0.0;

    int maxTiles = 10;
    int maxDepth = 8;

    int exportedTiles = 0;

    QSet<QString> seen;
};

static void traverseTile(const QJsonObject& tile,
                         const QUrl& baseUrl,
                         ExportContext& ctx,
                         int depth);

static void traverseTileset(const QJsonObject& tileset,
                            const QUrl& baseUrl,
                            ExportContext& ctx);

static void processContentUrl(const QUrl& url, ExportContext& ctx);

static void processContentUrl(const QUrl& url, ExportContext& ctx)
{
    if (ctx.exportedTiles >= ctx.maxTiles)
        return;

    QByteArray data = ctx.fetcher->get(url);
    if (data.isEmpty())
        return;

    // GLB binary glTF.
    if (data.size() >= 4 && data.mid(0, 4) == QByteArrayLiteral("glTF")) {
        int tileId = ctx.exportedTiles + 1;

        if (exportGlb(data, tileId, *ctx.writer)) {
            ++ctx.exportedTiles;
            qInfo() << "Exported GLB tile" << tileId << "from" << url;
        } else {
            qWarning() << "Could not export GLB tile from" << url;
        }

        return;
    }

    // Maybe external tileset JSON.
    QJsonParseError err;
    QJsonDocument doc = QJsonDocument::fromJson(data, &err);

    if (err.error == QJsonParseError::NoError && doc.isObject()) {
        QJsonObject obj = doc.object();

        if (obj.contains("root")) {
            traverseTileset(obj, url, ctx);
            return;
        }

        if (obj.contains("boundingVolume") ||
            obj.contains("content") ||
            obj.contains("children")) {
            traverseTile(obj, url, ctx, 0);
            return;
        }
    }

    qWarning() << "Unsupported content at" << url;
}

static void traverseTileset(const QJsonObject& tileset,
                            const QUrl& baseUrl,
                            ExportContext& ctx)
{
    QJsonObject root = tileset.value("root").toObject();
    if (root.isEmpty())
        root = tileset;

    traverseTile(root, baseUrl, ctx, 0);
}

static void traverseTile(const QJsonObject& tile,
                         const QUrl& baseUrl,
                         ExportContext& ctx,
                         int depth)
{
    if (ctx.exportedTiles >= ctx.maxTiles)
        return;

    if (depth > ctx.maxDepth)
        return;

    QJsonObject bv = tile.value("boundingVolume").toObject();

    if (!pointInBoundingVolume(bv, ctx.latRad, ctx.lonRad))
        return;

    if (tile.contains("content")) {
        QJsonObject content = tile.value("content").toObject();
        QString uri = content.value("uri").toString();

        if (!uri.isEmpty()) {
            QUrl u = resolveUrl(baseUrl, uri);
            u = ensureKey(u, ctx.apiKey);

            QString key = u.toString();

            if (!ctx.seen.contains(key)) {
                ctx.seen.insert(key);
                processContentUrl(u, ctx);
            }
        }
    }

    if (tile.contains("children")) {
        QJsonArray children = tile.value("children").toArray();

        for (const QJsonValue& v : children) {
            if (v.isObject())
                traverseTile(v.toObject(), baseUrl, ctx, depth + 1);
        }
    }
}

// ---------------------------------------------------------------------------
// Main.
// ---------------------------------------------------------------------------
int main(int argc, char* argv[])
{
    QCoreApplication app(argc, argv);

    if (argc < 4) {
        qInfo() << "Usage:";
        qInfo() << "  tiles2obj <apiKey> <latitude> <longitude> [outDir] [maxTiles] [maxDepth]";
        qInfo() << "";
        qInfo() << "Example:";
        qInfo() << "  tiles2obj YOUR_API_KEY 37.4219983 -122.0840335 output 10 8";
        return 1;
    }

    QString apiKey = QString::fromLocal8Bit(argv[1]);

    bool latOk = false;
    bool lonOk = false;

    double lat = QString::fromLocal8Bit(argv[2]).toDouble(&latOk);
    double lon = QString::fromLocal8Bit(argv[3]).toDouble(&lonOk);

    if (!latOk || !lonOk) {
        qCritical() << "Invalid latitude or longitude.";
        return 1;
    }

    QString outDir = QStringLiteral("output");
    if (argc > 4)
        outDir = QString::fromLocal8Bit(argv[4]);

    int maxTiles = 10;
    if (argc > 5)
        maxTiles = QString::fromLocal8Bit(argv[5]).toInt();

    int maxDepth = 8;
    if (argc > 6)
        maxDepth = QString::fromLocal8Bit(argv[6]).toInt();

    if (maxTiles <= 0)
        maxTiles = 1;

    if (maxDepth < 0)
        maxDepth = 0;

    Fetcher fetcher;
    ObjWriter writer;

    if (!writer.open(outDir)) {
        qCritical() << "Cannot open output directory:" << outDir;
        return 1;
    }

    ExportContext ctx;
    ctx.fetcher = &fetcher;
    ctx.writer = &writer;
    ctx.apiKey = apiKey;
    ctx.latRad = deg2rad(lat);
    ctx.lonRad = deg2rad(lon);
    ctx.maxTiles = maxTiles;
    ctx.maxDepth = maxDepth;
    ctx.exportedTiles = 0;

    // Official Google Photorealistic 3D Tiles root endpoint.
    // If Google changes this endpoint, update it here.
    QUrl rootUrl(QStringLiteral("https://tile.googleapis.com/v1/3dtiles/root.json"));
    rootUrl = ensureKey(rootUrl, apiKey);

    ctx.seen.insert(rootUrl.toString());

    qInfo() << "Requesting root tileset...";
    processContentUrl(rootUrl, ctx);

    writer.close();

    if (ctx.exportedTiles == 0) {
        qWarning() << "No tiles exported.";
        qWarning() << "Check API key, billing/API enablement, network/SSL,";
        qWarning() << "coordinate coverage, maxTiles/maxDepth, and Google terms.";
        return 2;
    }

    qInfo() << "Done.";
    qInfo() << "OBJ:" << writer.objPath;
    qInfo() << "MTL:" << writer.mtlPath;
    qInfo() << "Textures:" << writer.texDir;

    return 0;
}